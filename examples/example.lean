import Mathlib
import ProofStruct

/-!
This file is a small ProofStruct demo.

Recommended workflow:

1. Run `scripts/ProofStruct/batch_extract.py --file examples/example.lean`.
2. Open this file in VS Code.
3. Put the cursor on `#proof_blueprint demo_fermat` and inspect the Infoview.

The two bang commands below are shown as comments because they start generation from
inside Lean.  Uncomment them only when you intentionally want immediate generation.
-/

lemma demo_prime_as_int (p : ℕ) (hp : Nat.Prime p) : Prime (p : ℤ) := by
  exact Nat.prime_iff_prime_int.mp hp

theorem demo_fermat (p : ℕ) (a : ℤ) (hp : Nat.Prime p) (ha : ¬ (p : ℤ) ∣ a) :
    Int.ModEq (p : ℤ) (a ^ (p - 1)) 1 := by
  have hp_int : Prime (p : ℤ) := demo_prime_as_int p hp
  have hcoprime : IsCoprime a (p : ℤ) := by
    exact (hp_int.coprime_iff_not_dvd.mpr ha).symm
  exact Int.ModEq.pow_card_sub_one_eq_one hp hcoprime

theorem demo_compl_union (U : Type*) (A B : Set U) :
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

/-!
ProofStruct Infoview commands:

* `#proof_blueprint demo_fermat`
  Read existing JSON and display the blueprint.  This is the recommended default.

* `#proof_blueprint! demo_fermat`
  Generate the formal blueprint if it is missing, then display it.

* `#proof_blueprint_english! demo_fermat`
  Generate the English blueprint if it is missing, then display Formal/English views.
-/

#proof_blueprint demo_fermat

-- #proof_blueprint! demo_fermat
-- #proof_blueprint_english! demo_fermat
