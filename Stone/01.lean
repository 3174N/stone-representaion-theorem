import Mathlib.Tactic
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Ideal
import Mathlib.Order.PrimeIdeal

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
  : ∃ I' : Order.Ideal A, Order.Ideal.IsPrime I' ∧ I'.IsMaximal ∧ I'.IsProper ∧ I ≤ I' := by
  sorry


lemma nonzero_homomorphism (A : BoolAlg) (B : BoolAlg) (p : A) (pNonZero : p ≠ ⊥) :
  ∃ φ : A ⟶ B , φ p = ⊤ := by
  let I' := Order.Ideal.principal pᶜ
  have : pᶜ ≠ ⊤ := comp_non_bot_is_non_top A p pNonZero
  have hITProper : I'.IsProper := non_top_principal_is_proper A pᶜ this
  obtain ⟨ I, hI ⟩ := exists_maximal_ideal A I' hITProper
  obtain ⟨ hIPrime, hIMax, hIProper, hIGeIT ⟩ := hI

  classical
  let φ : BoundedLatticeHom A B := {
    toFun := fun a ↦ if a ∈ I then ⊥ else ⊤

    map_sup' := by
      intro a b
      split
      case isTrue h =>
        have hAAndBInI : a ∈ I ∧ b ∈ I := Order.Ideal.sup_mem_iff.mp h
        rw [if_pos hAAndBInI.left, if_pos hAAndBInI.right]
        exact Eq.symm (bot_sup_eq ⊥)
      case isFalse h =>
        have hAOrBNotInI : a ∉ I ∨ b ∉ I := by
          by_contra!
          have hACupBInI : a ⊔ b ∈ I := by
            exact Order.Ideal.sup_mem_iff.mpr this
          exact h hACupBInI
        cases hAOrBNotInI
        case inl hA =>
          rw [if_neg hA]
          exact Eq.symm (top_sup_eq (if b ∈ I then ⊥ else ⊤))
        case inr hB =>
          rw [if_neg hB]
          exact Eq.symm (sup_top_eq (if a ∈ I then ⊥ else ⊤))

    map_inf' := by
      intro a b
      split
      case isTrue h =>
        have hAOrBInI : a ∈ I ∨ b ∈ I := Order.Ideal.IsPrime.mem_or_mem hIPrime h
        cases hAOrBInI
        case inl h =>
          rw [if_pos h]
          exact Eq.symm (bot_inf_eq (if b ∈ I then ⊥ else ⊤))
        case inr h =>
          rw [if_pos h]
          exact Eq.symm (inf_bot_eq (if a ∈ I then ⊥ else ⊤))
      case isFalse h =>
        have hAAndBNotInI : a ∉ I ∧ b ∉ I := by
          rw [← @not_or]
          by_contra hc
          cases hc
          case inl hl =>
            have hAMeetBLeA : a ⊓ b ≤ a := inf_le_left
            have : a ⊓ b ∈ I := I.lower' hAMeetBLeA hl
            exact h this
          case inr hr =>
            have hAMeetBLeB : a ⊓ b ≤ b := inf_le_right
            have : a ⊓ b ∈ I := I.lower' hAMeetBLeB hr
            exact h this
        rw [if_neg hAAndBNotInI.left, if_neg hAAndBNotInI.right]
        exact Eq.symm (top_inf_eq ⊤)

    map_top' := by
      have : ⊤ ∉ I := Order.Ideal.IsProper.top_notMem hIProper
      rw [if_neg this]

    map_bot' := by
      have : ⊥ ∈ I := Order.Ideal.bot_mem I
      rw [if_pos this]
  }
  have hPhiPTop : φ p = ⊤ := by
    have : pᶜ ∈ I := Order.Ideal.principal_le_iff.mp hIGeIT
    have hPNotInI : p ∉ I := Order.Ideal.IsProper.notMem_of_compl_mem hIProper this
    have : φ.toFun p = ⊤ := if_neg hPNotInI
    exact this
  use BoolAlg.ofHom φ
  exact hPhiPTop
