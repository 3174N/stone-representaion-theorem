import Mathlib.Tactic
import Mathlib.Order.Ideal

variable {A : Type*} [BooleanAlgebra A]

lemma exists_maximal_ideal (I : Order.Ideal A):
  ∃ I' : Order.Ideal A, I'.IsMaximal ∧ I ≤ I' := by
  sorry

lemma nonzero_homomorphism (p : A) (pNonZero : p ≠ ⊥):
  ∃ φ : BoundedLatticeHom A Bool, φ p = ⊤ := by
  let I : Order.Ideal A := {
    carrier := { b | b ≤ p }

    nonempty' := by
      use ⊥
      have botLeP : ⊥ ≤ p := by exact OrderBot.bot_le p
      exact botLeP

    lower' := by
      unfold IsLowerSet
      intro a b hblea hainI
      have hblep : b ≤ p := by exact Std.IsPreorder.le_trans b a p hblea hainI
      exact hblep

    directed' := by
      unfold DirectedOn
      intro x hxI y hyI
      use x ⊔ y
      constructor
      · have hxylep : x ⊔ y ≤ p := by exact sup_le hxI hyI
        exact hxylep
      · exact ⟨ le_sup_left, le_sup_right ⟩
  }
  have hExMax : ∃ I' : Order.Ideal A, I'.IsMaximal ∧ I ≤ I' := by exact exists_maximal_ideal I
  obtain ⟨ I', hI' ⟩ := hExMax
  classical
  let φ : BoundedLatticeHom A Bool := {
    toFun := fun a ↦ if a ∈ I' then true else false

    map_sup' := by
      intro a b
      split
      case isTrue h =>
        have habInI : a ∈ I' ∧ b ∈ I' := by exact Order.Ideal.sup_mem_iff.mp h
        simp only [Bool.if_false_right, Bool.and_true, Bool.max_eq_or, Bool.true_eq,
          Bool.or_eq_true, decide_eq_true_eq]
        left
        exact habInI.left
      case isFalse h =>
        sorry

    map_inf' := by
      sorry

    map_bot' := by
      sorry

    map_top' := by
      sorry
  }
  use φ
  have hpInI : p ∈ I := by exact Order.Ideal.principal_le_iff.mp fun ⦃a⦄ a_1 ↦ a_1
  aesop
