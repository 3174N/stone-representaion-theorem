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
    hom_inv_id := by {
      ext A p
      simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj, BoolAlg.hom_comp,
        BoundedLatticeHom.comp_apply, NatTrans.id_app, BoolAlg.hom_id, BoundedLatticeHom.id_apply]
      let s : TopologicalSpace.Clopens (A ⟶ Two) := ⟨{φ | (ConcreteCategory.hom φ) p = ⊤},
              (fa_is_top_set_is_clopen ⟨ p, rfl ⟩)⟩
      have hStruct : (BoolAlg.Hom.hom (StoneIsomorphism A)) p =
          s := rfl
      erw [hStruct]
      unfold StoneIsomorphismInv
      dsimp
      change Classical.choose (StoneIsomorphismInv._proof_1 A s) = p
      have hChoose := Classical.choose_spec (StoneIsomorphismInv._proof_1 A s)
      have hSIsBasicP : s.carrier = basicSet p := by {
        rw [← hStruct]
        rfl
      }
      symm
      exact hChoose.2 p hSIsBasicP
    }
    inv_hom_id := by {
      ext A p
      simp only [Functor.comp_obj, NatTrans.comp_app, Functor.id_obj, BoolAlg.hom_comp,
        BoundedLatticeHom.comp_apply, NatTrans.id_app, BoolAlg.hom_id, BoundedLatticeHom.id_apply]
      let s := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen p))
      have : (BoolAlg.Hom.hom (StoneIsomorphismInv A)) p = s := rfl
      erw [this]
      obtain ⟨ a, ha ⟩ := clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen p)
      have : s = a := by {
        apply ha.2
        exact (Classical.choose_spec (StoneIsomorphismInv._proof_1 A p)).1
      }
      rw [this]
      let basicA : TopologicalSpace.Clopens (A ⟶ Two) := ⟨{φ | (ConcreteCategory.hom φ) a = ⊤},
              (fa_is_top_set_is_clopen ⟨ a, rfl ⟩)⟩
      have : (BoolAlg.Hom.hom (StoneIsomorphism A)) a =
          basicA := rfl
      erw [this]
      change (basicA : TopologicalSpace.Clopens _) = (p : TopologicalSpace.Clopens _)
      apply TopologicalSpace.Clopens.ext
      change basicSet a = p.carrier
      symm
      exact ha.1
    }
  }
  counitIso := StoneCounit
}
