import Mathlib.Tactic
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Ideal

-- variable {A : Type*} [BoolAlg]

lemma non_top_principal_is_proper (A : BoolAlg) (p : A) (hPNonTop : p ≠ ⊤)
  : (Order.Ideal.IsProper (Order.Ideal.principal p)) := by
  rw [@Order.Ideal.isProper_iff]
  rw [Set.ne_univ_iff_exists_notMem]
  let I := Order.Ideal.principal p
  have hTopNinI : ⊤ ∉ I := by
    by_contra!
    have hTopPEqTop : ⊤ ⊔ p = ⊤ := by exact top_sup_eq p
    have hTopPEqP : ⊤ ⊔ p = p := by exact sup_of_le_right this
    have hTIsP : ⊤ = p := by
      rw [←hTopPEqTop, hTopPEqP]
    have hPIsTop : p = ⊤ := by exact id (Eq.symm hTIsP)
    exact hPNonTop hPIsTop
  use ⊤
  exact hTopNinI

lemma comp_non_bot_is_non_top (A : BoolAlg) (p : A) (hPNonBot : p ≠ ⊥) : pᶜ ≠ ⊤ := by
  by_contra!
  have : p = ⊥ := by exact compl_eq_top.mp this
  exact hPNonBot this

lemma exists_maximal_ideal (A : BoolAlg) (I : Order.Ideal A) (hIProper : I.IsProper)
  : ∃ I' : Order.Ideal A, I'.IsProper ∧ I'.IsMaximal ∧ I ≤ I' := by
  sorry


lemma nonzero_homomorphism (A : BoolAlg) (B : BoolAlg) (p : A) (pNonZero : p ≠ ⊥) :
  ∃ φ : A ⟶ B , φ p = ⊤ := by
  let I := Order.Ideal.principal pᶜ
  have : pᶜ ≠ ⊤ := comp_non_bot_is_non_top A p pNonZero
  have IProper : I.IsProper := non_top_principal_is_proper A pᶜ this

  let φ : BoundedLatticeHom A B := sorry
  use BoolAlg.ofHom φ
  sorry
