import Stone.StoneRepresentationTheorem
import Stone.StoneCoIsomorphism

open CategoryTheory

noncomputable def StoneDuality : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := {
    hom := {
      app := fun A => StoneIsomorphism A
    }
    inv := {
      app := fun A => StoneIsomorphismInv A
      naturality := by {
        intro A B f
        rw [@BoolAlg.hom_ext_iff]
        rw [@BoundedLatticeHom.ext_iff]
        intro U
        change TopologicalSpace.Clopens (Hom2.obj A).unop at U
        obtain ⟨ϕ, h_U_basic_phi, h_phi_unique⟩ := clopen_basic_clopen U
        rw [@BoolAlg.coe_comp]
        rw [@BoolAlg.comp_apply]
        rw [@Function.comp_apply]
        rw [h_U_basic_phi]
        rw [basic_set_clop_hom_map]
        rw [basic_set_stone_inv_hom_map]
        rw [basic_set_stone_inv_hom_map]
        rw [@Functor.id_map]
        rfl
      }
    }
    hom_inv_id := by {sorry}
    inv_hom_id := by {sorry}
  }
  counitIso := StoneCounit
}
