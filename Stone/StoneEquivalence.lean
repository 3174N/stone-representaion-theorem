import Stone.StoneUnit
import Stone.StoneCounit

open CategoryTheory

lemma hom2_stone_iso_basic_hom {A : BoolAlg} {ϕ : A ⟶ Two} :
((Hom2.map (StoneIsomorphism A)).unop) (basicHom ϕ) = ϕ := by {
  rw [BoolAlg.ext_iff]
  intro a
  classical
  change (if ϕ ∈ (basicClopen a) then ⊤ else ⊥) = (ConcreteCategory.hom ϕ) a
  have h_phi_a_or : ϕ a = ⊤ ∨ ϕ a = ⊥ := by {
    rcases ϕ a
    · exact Or.inr rfl
    · exact Or.symm (Or.inr rfl)
  }
  rcases h_phi_a_or with h_phi_a_top | h_phi_a_bot
  · have h_phi_in_basic_a : ϕ ∈ (basicClopen a) := by {
      simp_all only [Functor.id_obj]
      exact h_phi_a_top
    }
    simp [h_phi_in_basic_a]
    exact id (Eq.symm h_phi_a_top)
  · have h_phi_nin_basic_a : ¬ ϕ ∈ (basicClopen a) := by {
      by_contra!
      have h_phi_a_top : ϕ a = ⊤ := by {exact this}
      simp_all only [top_ne_bot]
    }
    simp [h_phi_nin_basic_a]
    exact id (Eq.symm h_phi_a_bot)
}

noncomputable def StoneDuality : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := StoneUnit
  counitIso := StoneCounit
  functor_unitIso_comp := by {
    intro A
    apply Opposite.unop_injective
    ext ϕ
    exact hom2_stone_iso_basic_hom
  }
}
