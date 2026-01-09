import Mathlib.Order.Category.BoolAlg
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Clopen
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory

def Two : BoolAlg := BoolAlg.of Bool
instance : TopologicalSpace Two := ⊥
instance : DiscreteTopology Two := ⟨rfl⟩
instance : ContinuousInf Two := ⟨continuous_of_discreteTopology⟩
instance : ContinuousSup Two := ⟨continuous_of_discreteTopology⟩
instance : Finite Two := Finite.of_fintype Bool
def stoneEmbed (A : BoolAlg) : (A ⟶ Two) → (A → Bool) := fun f a => f a
instance (A : BoolAlg) : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (stoneEmbed A) inferInstance
instance (A : BoolAlg) : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (fun f ↦ (f : A → Two)) inferInstance



lemma stone_space_is_compact (A : BoolAlg) : CompactSpace (TopCat.of (A ⟶ Two)).carrier := by {
  let Prod := A → Two
  let Homs : Set Prod := { φ |  φ : (A ⟶ Two) }
  have hProdImpliesHom :
    IsCompact (Set.univ : Set Prod) → CompactSpace (TopCat.of (A ⟶ Two)) := by {
    intro hProdCompact
    have hHomIsClosed : IsClosed Homs := by {
      have hHomsAreHoms : Homs = { f : Prod |
        (∀ x y, f (x ⊓ y) = f x ⊓ f y) ∧
        (∀ x y, f (x ⊔ y) = f x ⊔ f y) ∧
        (f ⊤ = ⊤) ∧
        (f ⊥ = ⊥) } := by {
          ext f
          constructor
          · rintro ⟨hom, rfl⟩
            exact ⟨hom.hom.map_inf', hom.hom.map_sup', hom.hom.map_top', hom.hom.map_bot'⟩
          · rintro ⟨h_inf, h_sup, h_top, h_bot⟩
            use BoolAlg.ofHom {
              toFun := f
              map_inf' := h_inf
              map_sup' := h_sup
              map_top' := h_top
              map_bot' := h_bot
            }
            rfl
      }
      rw [hHomsAreHoms]
      apply IsClosed.inter
      · change IsClosed { f : A → Two | ∀ (x y : A), f (x ⊓ y) = f x ⊓ f y }
        simp [Set.setOf_forall]
        apply isClosed_iInter
        intro x
        apply isClosed_iInter
        intro y
        apply isClosed_eq
        · exact continuous_apply (x ⊓ y)
        · apply Continuous.inf
          · exact continuous_apply x
          · exact continuous_apply y
      · apply IsClosed.inter
        · change IsClosed { f : A → Two | ∀ (x y : A), f (x ⊔ y) = f x ⊔ f y }
          simp [Set.setOf_forall]
          apply isClosed_iInter
          intro x
          apply isClosed_iInter
          intro y
          apply isClosed_eq
          · exact continuous_apply (x ⊔ y)
          · apply Continuous.sup
            · exact continuous_apply x
            · exact continuous_apply y
        · apply IsClosed.inter
          · apply isClosed_eq
            · exact continuous_apply ⊤
            · exact continuous_const
          · apply isClosed_eq
            · exact continuous_apply ⊥
            · exact continuous_const
    }
    have hHomsSSProd : Homs ⊆ (Set.univ : Set Prod) := fun ⦃a⦄ a_1 ↦ trivial
    have hHomsCompact :
      IsCompact Homs := IsCompact.of_isClosed_subset hProdCompact hHomIsClosed hHomsSSProd

    have : Topology.IsInducing (fun f : A ⟶ Two ↦ (f : Prod)) := by {
      exact { eq_induced := rfl }
    }
    rw [←isCompact_univ_iff]
    rw [this.isCompact_iff]
    convert hHomsCompact
    ext f
    simp [Homs, Set.image_univ, Set.mem_range]
    exact Iff.symm Set.mem_setOf
  }

  apply hProdImpliesHom
  exact CompactSpace.isCompact_univ
}

lemma stone_space_is_hausdorrf (A : BoolAlg) : T2Space (TopCat.of (A ⟶ Two)).carrier := by {
  sorry
}

lemma stone_space_is_totally_disconnected (A : BoolAlg)
  : TotallyDisconnectedSpace (TopCat.of (A ⟶ Two)).carrier := by {
  sorry
}

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
