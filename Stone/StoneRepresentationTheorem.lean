import Mathlib.Order.Category.BoolAlg
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Clopen
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Hom.BoundedLattice

open CategoryTheory


def Clop : Profiniteᵒᵖ ⥤ BoolAlg := by refine {
    obj := fun X => BoolAlg.of (TopologicalSpace.Clopens X.unop)
    map := by {
      intro X Y f
      let ClopX : BoolAlg := BoolAlg.of (TopologicalSpace.Clopens X.unop)
      let ClopY : BoolAlg := BoolAlg.of (TopologicalSpace.Clopens Y.unop)
      let g : BoundedLatticeHom ClopX ClopY := {
        toFun := by {
          intro U
          let V := f.unop.hom' ⁻¹' U
          use V

          simp [IsClopen, IsOpen]
          obtain ⟨Uval, hUIsClopen⟩ := U
          constructor
          · obtain ⟨hUIsClosed, hUIsOpen⟩ := hUIsClopen
            apply IsClosed.preimage f.unop.hom'.continuous_toFun hUIsClosed
          · apply f.unop.hom'.continuous_toFun.isOpen_preimage
            exact IsClopen.isOpen hUIsClopen
        }
        map_sup' := by {
          intro a b
          let finva := f.unop.hom' ⁻¹' a
          let finvb := f.unop.hom' ⁻¹' b
          let finvab := f.unop.hom' ⁻¹' (a ⊔ b)
          suffices finva ⊔ finvb = finvab by {
            exact rfl
          }
          simp [max, SemilatticeSup.sup]
          unfold finvab
          rw [@Set.Subset.antisymm_iff]
          constructor
          · intro x xInInvfaOrInvfb
            rw [Set.mem_preimage]
            simp [max, SemilatticeSup.sup]
            unfold finva finvb at xInInvfaOrInvfb
            rcases xInInvfaOrInvfb with xInfinva | xInfinvb
            · exact Or.symm (Or.inr xInfinva)
            · exact Or.symm (Or.inl xInfinvb)
          · intro x xInInvfaorb
            simp [Set.mem_preimage] at xInInvfaorb
            simp [Set.mem_union]
            unfold finva finvb
            rcases xInInvfaorb with fxIna | fxInb
            · exact Or.symm (Or.inr fxIna)
            · exact Or.symm (Or.inl fxInb)
        }
        map_inf' := sorry
        map_top' := sorry
        map_bot' := sorry
      }
      use g
      · exact g.map_top'
      · exact g.map_bot'
    }
}

def Hom2 : BoolAlg ⥤ Profiniteᵒᵖ := by refine {
  sorry
}

def StoneRepresentationEquivalence : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := by sorry
  counitIso := by sorry
}
