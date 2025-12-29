import Mathlib.Tactic

variable {A : Type*} [BooleanAlgebra A]

lemma nonzero_homomorphism (p : A) (pNonZero : p ≠ ⊥):
  ∃ φ: BoundedLatticeHom A Bool, φ p = ⊤ := by
  let I : Set A := { b | p ≥ b }
  have hpI : p ∈ I := by exact
  have hiIideal: Ideal I := by exact
