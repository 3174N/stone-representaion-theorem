import Mathlib.Order.Category.BoolAlg
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Clopen
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Hom.BoundedLattice

open CategoryTheory

def Two : BoolAlg := BoolAlg.of Bool
def stoneEmbed (A : BoolAlg) : (A ⟶ Two) → (A → Bool) := fun f a => f a
instance (A : BoolAlg) : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (stoneEmbed A) inferInstance

lemma stone_space_is_compact (A : BoolAlg) : CompactSpace (TopCat.of (A ⟶ Two)).carrier := sorry

lemma stone_space_is_hausdorrf (A : BoolAlg) : T2Space (TopCat.of (A ⟶ Two)).carrier := sorry

lemma stone_space_is_totally_disconnected (A : BoolAlg) : TotallyDisconnectedSpace (TopCat.of (A ⟶ Two)).carrier := sorry

lemma clopen_iff_exact_fa_is_top {A : BoolAlg} (U : Set (TopCat.of (A ⟶ Two))) (hUIsClopen : IsClopen U) :
  ∀ (U : Set (TopCat.of (A ⟶ Two))), IsClopen U ↔ ∃ a : A, U = {ϕ | ϕ a = ⊤} := sorry


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
        map_sup' := by exact fun a b ↦ rfl
        map_inf' := by exact fun a b ↦ rfl
        map_top' := by exact rfl
        map_bot' := by exact rfl
      }
      use g
      · exact g.map_top'
      · exact g.map_bot'
    }
}

def Hom2 : BoolAlg ⥤ Profiniteᵒᵖ := by refine {
  obj := by {
    intro A
    use TopCat.of (A ⟶ Two)
    · exact stone_space_is_totally_disconnected A
    · exact stone_space_is_compact A
    · exact stone_space_is_hausdorrf A
  }
  map := by {
    intro A B f
    let HomA2 := TopCat.of (A ⟶ Two)
    let HomB2 :=  TopCat.of (B ⟶ Two)
    let g : HomB2 → HomA2 := fun ϕ ↦ (f ≫ ϕ)
    use g
    rw [@continuous_def]
    intro s hsIsOpen
    sorry
  }
}

def StoneRepresentationEquivalence : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := by sorry
  counitIso := by sorry
}
