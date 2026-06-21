import Mathlib
import ProofStruct

theorem fermat_little_theorem_1 (p : ℕ) (a : ℤ) (hp : Nat.Prime p) (ha : ¬ (p : ℤ) ∣ a) :
    Int.ModEq (p : ℤ) (a ^ (p - 1)) 1 := by
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcoprime : IsCoprime a (p : ℤ) := by
    exact (hp_int.coprime_iff_not_dvd.mpr ha).symm
  exact Int.ModEq.pow_card_sub_one_eq_one hp hcoprime

#proof_blueprint fermat_little_theorem_1

theorem fermat_little_theorem_2 (p : ℕ) (a : ℤ) (hp : Nat.Prime p) (ha : ¬ (p : ℤ) ∣ a) :
    Int.ModEq (p : ℤ) (a ^ (p - 1)) 1 := by
  have hprime_as_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have ha_coprime : IsCoprime a (p : ℤ) :=
    (hprime_as_int.coprime_iff_not_dvd.mpr ha).symm
  simpa using Int.ModEq.pow_card_sub_one_eq_one hp ha_coprime

#proof_blueprint fermat_little_theorem_2

theorem fermat_little_theorem_base_2 (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) :
    Int.ModEq (p : ℤ) ((2 : ℤ) ^ (p - 1)) 1 := by
  have hp_not_two : p ≠ 2 := by
    intro hp_eq
    subst p
    rcases hodd with ⟨k, hk⟩
    omega
  have h_two_not_dvd : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro hdiv
    have hdiv_nat : p ∣ 2 := by
      exact_mod_cast hdiv
    have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv_nat
    exact hp_not_two (le_antisymm hp_le_two hp.two_le)
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcoprime_two : IsCoprime (2 : ℤ) (p : ℤ) := by
    exact (hp_int.coprime_iff_not_dvd.mpr h_two_not_dvd).symm
  exact Int.ModEq.pow_card_sub_one_eq_one hp hcoprime_two

#proof_blueprint fermat_little_theorem_base_2


theorem fermat_little_theorem_mod_5 (a : ℤ) (ha : ¬ (5 : ℤ) ∣ a) :
    Int.ModEq (5 : ℤ) (a ^ 4) 1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp_int : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcoprime : IsCoprime a (5 : ℤ) := by
    exact (hp_int.coprime_iff_not_dvd.mpr ha).symm
  have hfermat : Int.ModEq (5 : ℤ) (a ^ (5 - 1)) 1 :=
    Int.ModEq.pow_card_sub_one_eq_one hp hcoprime
  simpa using hfermat


theorem fermat_little_theorem_mod_7 (a : ℤ) (ha : ¬ (7 : ℤ) ∣ a) :
    Int.ModEq (7 : ℤ) (a ^ 6) 1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hp_int : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcoprime : IsCoprime a (7 : ℤ) := by
    exact (hp_int.coprime_iff_not_dvd.mpr ha).symm
  have hfermat : Int.ModEq (7 : ℤ) (a ^ (7 - 1)) 1 :=
    Int.ModEq.pow_card_sub_one_eq_one hp hcoprime
  simpa using hfermat


theorem test_theorem_1 (p a b : ℤ) (hp : Prime p) (hab : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hcoprime : IsCoprime p a := hp.coprime_iff_not_dvd.mpr hpa
    exact hcoprime.dvd_of_dvd_mul_left hab


theorem test_theorem_2 (m n : ℕ) (a b : ℤ) (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) :
    ∃ x : ℤ, Int.ModEq (m : ℤ) x a ∧ Int.ModEq (n : ℤ) x b := by
  have _hm_ne : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have _hn_ne : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  let r : ℤ := Nat.gcdA m n
  let s : ℤ := Nat.gcdB m n
  have hbezout : (m : ℤ) * r + (n : ℤ) * s = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [← h, hmn.gcd_eq_one]
    norm_num
  refine ⟨b * (r * (m : ℤ)) + a * (s * (n : ℤ)), ?_, ?_⟩
  · have h_left_zero : b * (r * (m : ℤ)) ≡ 0 [ZMOD (m : ℤ)] := by
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨b * r, by ring⟩
    have h_right_one : s * (n : ℤ) ≡ 1 [ZMOD (m : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨r, ?_⟩
      rw [← hbezout]
      ring
    calc
      b * (r * (m : ℤ)) + a * (s * (n : ℤ))
          ≡ 0 + a * 1 [ZMOD (m : ℤ)] := h_left_zero.add (h_right_one.mul_left a)
      _ = a := by ring
  · have h_left_one : r * (m : ℤ) ≡ 1 [ZMOD (n : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨s, ?_⟩
      rw [← hbezout]
      ring
    have h_right_zero : a * (s * (n : ℤ)) ≡ 0 [ZMOD (n : ℤ)] := by
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨a * s, by ring⟩
    calc
      b * (r * (m : ℤ)) + a * (s * (n : ℤ))
          ≡ b * 1 + 0 [ZMOD (n : ℤ)] := (h_left_one.mul_left b).add h_right_zero
      _ = b := by ring

#proof_blueprint test_theorem_2

theorem test_theorem_3 (F V W : Type*) [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V] (T : V →ₗ[F] W) :
    Module.finrank F V =
      Module.finrank F (LinearMap.ker T) + Module.finrank F (LinearMap.range T) := by
  have h_rank_nullity :
      Module.finrank F (LinearMap.range T) + Module.finrank F (LinearMap.ker T) =
        Module.finrank F V :=
    LinearMap.finrank_range_add_finrank_ker T
  rw [← h_rank_nullity]
  omega


theorem test_theorem_4 (F V W : Type*) [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (T : V →ₗ[F] W) :
    Function.Injective (fun v : V => T v) ↔ LinearMap.ker T = ⊥ := by
  constructor
  · intro hT
    ext v
    constructor
    · intro hv
      change v = 0
      apply hT
      simpa using hv
    · intro hv
      have hv0 : v = 0 := by
        simpa using hv
      simp [hv0]
  · intro hker u v huv
    have hdiff_mem : u - v ∈ LinearMap.ker T := by
      change T (u - v) = 0
      simp [map_sub, huv]
    have hdiff_zero : u - v = 0 := by
      have : u - v ∈ (⊥ : Submodule F V) := by
        simpa [hker] using hdiff_mem
      simpa using this
    exact sub_eq_zero.mp hdiff_zero


theorem test_theorem_5 (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (T : V →ₗ[F] V) (v w : V) (lambda mu : F)
    (hv_ne : v ≠ 0) (hw_ne : w ≠ 0) (hlambda : T v = lambda • v)
    (hmu : T w = mu • w) (hdiff : lambda ≠ mu) :
    ∀ a b : F, a • v + b • w = 0 → a = 0 ∧ b = 0 := by
  intro a b hrel
  have h_apply : a • (lambda • v) + b • (mu • w) = 0 := by
    have hTrel : T (a • v + b • w) = 0 := by
      simp [hrel]
    simpa [map_add, hlambda, hmu] using hTrel
  have h_lambda_mul : a • (lambda • v) + b • (lambda • w) = 0 := by
    have hscaled : lambda • (a • v + b • w) = 0 := by
      simp [hrel]
    simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hb_smul : (b * (mu - lambda)) • w = 0 := by
    have hsub :
        (a • (lambda • v) + b • (mu • w)) -
            (a • (lambda • v) + b • (lambda • w)) = 0 := by
      rw [h_apply, h_lambda_mul, sub_self]
    have htmp : b • ((mu - lambda) • w) = 0 := by
      calc
        b • ((mu - lambda) • w) = b • (mu • w) - b • (lambda • w) := by
          rw [sub_smul, smul_sub]
        _ = (a • (lambda • v) + b • (mu • w)) -
            (a • (lambda • v) + b • (lambda • w)) := by
          abel
        _ = 0 := hsub
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hmu_sub : mu - lambda ≠ 0 := sub_ne_zero.mpr hdiff.symm
  have hb : b = 0 := by
    rcases smul_eq_zero.mp hb_smul with hbmul | hw
    · exact (mul_eq_zero.mp hbmul).resolve_right hmu_sub
    · exact False.elim (hw_ne hw)
  have ha_smul : a • v = 0 := by
    simpa [hb] using hrel
  have ha : a = 0 := by
    rcases smul_eq_zero.mp ha_smul with ha | hv
    · exact ha
    · exact False.elim (hv_ne hv)
  exact ⟨ha, hb⟩


theorem test_theorem_6 (G : Type*) [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  have h_cosets_count : Nat.card H ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card H
  exact h_cosets_count


theorem test_theorem_7 (G K : Type*) [Group G] [Group K] (phi : G →* K) :
    Subgroup.Normal (phi.ker) := by
  have hnormal : Subgroup.Normal (phi.ker) := by
    infer_instance
  exact hnormal


theorem test_theorem_8 (G : Type*) [Group G] (H : Subgroup G) :
    (∃ g : G, Subgroup.closure ({g} : Set G) = ⊤) →
      ∃ h : H, Subgroup.closure ({h} : Set H) = ⊤ := by
  intro hG
  have hcyclic : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    rcases hG with ⟨g, hg⟩
    exact ⟨g, by simpa [Subgroup.zpowers_eq_closure] using hg⟩
  have hH : IsCyclic H := Subgroup.isCyclic H
  rw [isCyclic_iff_exists_zpowers_eq_top] at hH
  rcases hH with ⟨h, hh⟩
  exact ⟨h, by simpa [Subgroup.zpowers_eq_closure] using hh⟩


theorem test_theorem_9 (A : Type*) :
    ¬ ∃ f : A → Set A, Function.Surjective f := by
  rintro ⟨f, hf⟩
  let D : Set A := {x | x ∉ f x}
  rcases hf D with ⟨a, ha⟩
  have hmem : a ∈ D ↔ a ∉ f a := Iff.rfl
  have hdiag : a ∈ D ↔ a ∉ D := by
    exact hmem.trans (by rw [ha])
  have hnot : a ∉ D := fun hD => hdiag.mp hD hD
  have hin : a ∈ D := hdiag.mpr hnot
  exact hnot hin


theorem test_theorem_10 (U : Type*) (A B : Set U) :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro hx
    constructor
    · intro hxA
      exact hx (Or.inl hxA)
    · intro hxB
      exact hx (Or.inr hxB)
  · intro hx hxAB
    rcases hxAB with hxA | hxB
    · exact hx.1 hxA
    · exact hx.2 hxB
