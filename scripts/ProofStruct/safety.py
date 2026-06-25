from __future__ import annotations

import fcntl
import json
import os
import time
import tomllib
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from types import TracebackType
from typing import Self


GIB = 1024 ** 3


class SafetyError(RuntimeError):
    pass


@dataclass(frozen=True)
class InstantSafetyConfig:
    enabled: bool = False
    max_lean_processes: int = 8
    min_available_memory_gb: float = 10.0
    timeout_seconds: int = 180
    lock_wait_seconds: int = 300


@dataclass(frozen=True)
class LeanProcessInfo:
    pid: int
    command: str


def _as_bool(value: object, default: bool) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "on"}
    return default


def _as_int(value: object, default: int) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return default
    return default


def _as_float(value: object, default: float) -> float:
    if isinstance(value, int | float):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return default
    return default


def load_instant_safety_config(path: Path | None) -> InstantSafetyConfig:
    config = InstantSafetyConfig()
    if path is None or not path.exists():
        return config
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    instant = data.get("instant")
    if not isinstance(instant, dict):
        return config
    return InstantSafetyConfig(
        enabled=_as_bool(instant.get("enabled"), config.enabled),
        max_lean_processes=max(0, _as_int(instant.get("max_lean_processes"), config.max_lean_processes)),
        min_available_memory_gb=max(
            0.0,
            _as_float(instant.get("min_available_memory_gb"), config.min_available_memory_gb),
        ),
        timeout_seconds=max(1, _as_int(instant.get("timeout_seconds"), config.timeout_seconds)),
        lock_wait_seconds=max(0, _as_int(instant.get("lock_wait_seconds"), config.lock_wait_seconds)),
    )


def apply_safety_overrides(
    config: InstantSafetyConfig,
    *,
    max_lean_processes: int | None = None,
    min_available_memory_gb: float | None = None,
    timeout_seconds: int | None = None,
    lock_wait_seconds: int | None = None,
) -> InstantSafetyConfig:
    updates: dict[str, object] = {}
    if max_lean_processes is not None:
        updates["max_lean_processes"] = max(0, max_lean_processes)
    if min_available_memory_gb is not None:
        updates["min_available_memory_gb"] = max(0.0, min_available_memory_gb)
    if timeout_seconds is not None:
        updates["timeout_seconds"] = max(1, timeout_seconds)
    if lock_wait_seconds is not None:
        updates["lock_wait_seconds"] = max(0, lock_wait_seconds)
    return replace(config, **updates)


def available_memory_gib() -> float | None:
    meminfo = Path("/proc/meminfo")
    if not meminfo.exists():
        return None
    for line in meminfo.read_text(encoding="utf-8").splitlines():
        if not line.startswith("MemAvailable:"):
            continue
        parts = line.split()
        if len(parts) < 2:
            return None
        try:
            return int(parts[1]) * 1024 / GIB
        except ValueError:
            return None
    return None


def _read_cmdline(pid_dir: Path) -> str | None:
    try:
        raw = (pid_dir / "cmdline").read_bytes()
    except OSError:
        return None
    if not raw:
        return None
    return " ".join(part.decode("utf-8", errors="replace") for part in raw.split(b"\0") if part)


def _is_lean_related_command(command: str) -> bool:
    parts = command.split()
    if not parts:
        return False
    executable = Path(parts[0]).name
    return executable == "lean" or executable == "lake"


def lean_processes() -> list[LeanProcessInfo]:
    current_pid = os.getpid()
    processes: list[LeanProcessInfo] = []
    for pid_dir in Path("/proc").iterdir():
        if not pid_dir.name.isdigit():
            continue
        pid = int(pid_dir.name)
        if pid == current_pid:
            continue
        command = _read_cmdline(pid_dir)
        if command is None or not _is_lean_related_command(command):
            continue
        processes.append(LeanProcessInfo(pid=pid, command=command))
    return sorted(processes, key=lambda item: item.pid)


class ProofStructSafetyGuard:
    def __init__(self, *, output_root: Path, config: InstantSafetyConfig) -> None:
        self.output_root = output_root
        self.config = config
        self.state_root = output_root / ".proofstruct"
        self.logs_root = self.state_root / "logs"
        self.lock_path = output_root / ".proofstruct.lock"
        self._lock_file = None
        self._log_path: Path | None = None
        self._started_at = time.time()

    @property
    def log_path(self) -> Path | None:
        return self._log_path

    def __enter__(self) -> Self:
        self.output_root.mkdir(parents=True, exist_ok=True)
        self.logs_root.mkdir(parents=True, exist_ok=True)
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        self._log_path = self.logs_root / f"instant-{timestamp}-{os.getpid()}.jsonl"
        self._acquire_lock()
        try:
            self._check_process_count()
            self._check_memory()
            self._log("guard_acquired", status="ok")
        except BaseException:
            self._release_lock()
            raise
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        tb: TracebackType | None,
    ) -> bool:
        elapsed = time.time() - self._started_at
        if exc is None:
            self._log("guard_released", status="ok", elapsed_seconds=elapsed)
        else:
            self._log(
                "guard_released",
                status="error",
                elapsed_seconds=elapsed,
                error=f"{type(exc).__name__}: {exc}",
            )
        self._release_lock()
        return False

    def _acquire_lock(self) -> None:
        self._lock_file = self.lock_path.open("a+", encoding="utf-8")
        wait_started_at = time.monotonic()
        deadline = wait_started_at + self.config.lock_wait_seconds
        logged_waiting = False
        while True:
            try:
                fcntl.flock(self._lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError as exc:
                elapsed = time.monotonic() - wait_started_at
                if self.config.lock_wait_seconds == 0 or time.monotonic() >= deadline:
                    self._log(
                        "lock_check",
                        status="blocked",
                        waited_seconds=elapsed,
                        lock_wait_seconds=self.config.lock_wait_seconds,
                    )
                    raise SafetyError(
                        "timed out waiting for another ProofStruct extraction to finish "
                        f"after {elapsed:.1f} seconds"
                    ) from exc
                if not logged_waiting:
                    self._log(
                        "lock_check",
                        status="waiting",
                        lock_wait_seconds=self.config.lock_wait_seconds,
                    )
                    logged_waiting = True
                time.sleep(0.5)
        self._log("lock_check", status="ok")
        self._lock_file.seek(0)
        self._lock_file.truncate()
        self._lock_file.write(
            json.dumps(
                {
                    "pid": os.getpid(),
                    "started_at": datetime.now(timezone.utc).isoformat(),
                },
                ensure_ascii=False,
            )
            + "\n"
        )
        self._lock_file.flush()

    def _release_lock(self) -> None:
        if self._lock_file is None:
            return
        try:
            fcntl.flock(self._lock_file.fileno(), fcntl.LOCK_UN)
        finally:
            self._lock_file.close()
            self._lock_file = None

    def _check_process_count(self) -> None:
        processes = lean_processes()
        count = len(processes)
        self._log(
            "process_check",
            status="ok" if count <= self.config.max_lean_processes else "blocked",
            count=count,
            max_lean_processes=self.config.max_lean_processes,
            processes=[process.__dict__ for process in processes],
        )
        if count > self.config.max_lean_processes:
            detail = "\n".join(f"  pid={p.pid}: {p.command}" for p in processes[:8])
            raise SafetyError(
                "too many Lean-related processes are running "
                f"({count} > {self.config.max_lean_processes}).\n{detail}"
            )

    def _check_memory(self) -> None:
        available = available_memory_gib()
        self._log(
            "memory_check",
            status="ok"
            if available is None or available >= self.config.min_available_memory_gb
            else "blocked",
            available_memory_gib=available,
            min_available_memory_gb=self.config.min_available_memory_gb,
        )
        if available is not None and available < self.config.min_available_memory_gb:
            raise SafetyError(
                "not enough available memory for ProofStruct extraction "
                f"({available:.2f} GiB < {self.config.min_available_memory_gb:.2f} GiB)"
            )

    def _log(self, event: str, **payload: object) -> None:
        if self._log_path is None:
            return
        record = {
            "event": event,
            "time": datetime.now(timezone.utc).isoformat(),
            **payload,
        }
        with self._log_path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
