import Mathlib.Order.Category.BoolAlg
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Clopen
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.FunLike.Basic

open CategoryTheory

def Two : BoolAlg := BoolAlg.of Bool
instance : TopologicalSpace Two := ⊥
instance : DiscreteTopology Two := ⟨rfl⟩
instance : ContinuousInf Two := ⟨continuous_of_discreteTopology⟩
instance : ContinuousSup Two := ⟨continuous_of_discreteTopology⟩
instance : Finite Two := Finite.of_fintype Bool
instance : T2Space Two := DiscreteTopology.toT2Space
def stoneEmbed (A : BoolAlg) : (A ⟶ Two) → (A → Bool) := fun f a => f a
instance (A : BoolAlg) : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (stoneEmbed A) inferInstance
instance (A : BoolAlg) : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (fun f ↦ (f : A → Two)) inferInstance



instance stone_space_is_compact (A : BoolAlg) : CompactSpace (TopCat.of (A ⟶ Two)).carrier := by {
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
        simp only [Set.setOf_forall]
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
          simp only [Set.setOf_forall]
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

    have : Topology.IsInducing (fun f : A ⟶ Two ↦ (f : Prod)) := {eq_induced := rfl}
    rw [←isCompact_univ_iff, this.isCompact_iff]
    convert hHomsCompact
    ext f
    simp only [Set.image_univ, Set.mem_range, Homs]
    exact Set.mem_setOf.symm
  }

  apply hProdImpliesHom
  exact CompactSpace.isCompact_univ
}

instance stone_space_is_hausdorff (A : BoolAlg) : T2Space (TopCat.of (A ⟶ Two)).carrier := by {
  let Homs : Set (A → Two) := { φ |  φ : (A ⟶ Two) }

  have hInducing : Topology.IsInducing (fun f : A ⟶ Two ↦ (f : (A → Two))) := {
    eq_induced := rfl
  }
  let g : (A ⟶ Two) → Homs := fun f ↦ ⟨ConcreteCategory.hom f, by simp [Homs]⟩
  have hEmbedding: Topology.IsEmbedding g := {
    eq_induced := by {
      rw [hInducing.eq_induced, Topology.IsEmbedding.subtypeVal.eq_induced]
      rw [induced_compose]
      rfl
    }

    injective := by {
      intro x y h
      apply ConcreteCategory.hom_ext
      exact congr_fun (Subtype.mk_eq_mk.mp h)
    }
  }

  exact hEmbedding.t2Space
}

instance stone_space_is_totally_disconnected (A : BoolAlg)
  : TotallyDisconnectedSpace (TopCat.of (A ⟶ Two)).carrier := by {
  let Homs : Set (A → Two) := { φ |  φ : (A ⟶ Two) }

  have hInducing : Topology.IsInducing (fun f : A ⟶ Two ↦ (f : (A → Two))) := {
    eq_induced := rfl
  }
  let g : (A ⟶ Two) → Homs := fun f ↦ ⟨ConcreteCategory.hom f, by simp [Homs]⟩
  have hEmbedding: Topology.IsEmbedding g := {
    eq_induced := by {
      rw [hInducing.eq_induced, Topology.IsEmbedding.subtypeVal.eq_induced, induced_compose]
      rfl
    }

    injective := by {
      intro x y h
      apply ConcreteCategory.hom_ext
      exact congr_fun (Subtype.mk_eq_mk.mp h)
    }
  }
  refine ⟨fun t _ ht_pre => ?_⟩
  have h_img_pre : IsPreconnected (g '' t) := hEmbedding.isPreconnected_image.mpr ht_pre
  have h_img_sub : (g '' t).Subsingleton :=
    IsPreconnected.subsingleton h_img_pre
  exact hEmbedding.injective.subsingleton_image_iff.mp h_img_sub
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
        toFun U := by {
          use f.unop.hom' ⁻¹' U
          simp only [IsClopen, IsOpen]
          obtain ⟨Uval, hUIsClopen⟩ := U
          constructor
          · obtain ⟨hUIsClosed, hUIsOpen⟩ := hUIsClopen
            apply IsClosed.preimage f.unop.hom'.continuous_toFun hUIsClosed
          · apply f.unop.hom'.continuous_toFun.isOpen_preimage
            exact IsClopen.isOpen hUIsClopen
        }
        map_sup' a b := rfl
        map_inf' a b := rfl
        map_top' := rfl
        map_bot' := rfl
      }
      use g
      · exact g.map_top'
      · exact g.map_bot'
    }
}

def Hom2 : BoolAlg ⥤ Profiniteᵒᵖ := by refine {
  obj := fun A => ⟨TopCat.of (A ⟶ Two), stone_space_is_totally_disconnected A⟩
  map := by {
    intro A B f
    let HomA2 := TopCat.of (A ⟶ Two)
    let HomB2 :=  TopCat.of (B ⟶ Two)
    use fun ϕ ↦ (f ≫ ϕ)
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    dsimp
    exact (continuous_apply (f a)).comp continuous_induced_dom
  }
}

def StoneRepresentationEquivalence : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := by sorry
  counitIso := by sorry
}
