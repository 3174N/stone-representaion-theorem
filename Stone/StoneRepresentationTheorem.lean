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
instance {A : BoolAlg} : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (stoneEmbed A) inferInstance
def stoneSubbasis (A : BoolAlg) : Set (Set (TopCat.of (A ⟶ Two))) :=
  {U | ∃ a : A, U = {ϕ : TopCat.of (A ⟶ Two) | ϕ a = ⊤}}

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

lemma projection_is_continuous {A : BoolAlg} {a : A} : Continuous fun (p : A ⟶ Two) => p a := by sorry
lemma fa_is_b_set_is_closed {A : BoolAlg} {a : A} {b : Two} :
IsClosed {ϕ : TopCat.of (A ⟶ Two) | ϕ a = b} := by {
  let U := {ϕ : TopCat.of (A ⟶ Two) | ϕ a = b}
  let PiA := fun (p : A ⟶ Two) => p a
  have ContPiA : Continuous PiA := by exact projection_is_continuous
  have UIsPreImOfbByProjA : U = PiA⁻¹' {b} := rfl
  have hSingletonIsClosed : IsClosed {b} := isClosed_singleton
  exact IsClosed.preimage ContPiA hSingletonIsClosed
}
lemma fa_is_top_set_is_clopen {A : BoolAlg} {U : Set (TopCat.of (A ⟶ Two))}
  (hUIsSetOfFaT : ∃ a : A, U = {ϕ | ϕ a = ⊤}) : IsClopen U := by {
    obtain ⟨a, h⟩ := hUIsSetOfFaT
    constructor
    · rw [h]
      exact fa_is_b_set_is_closed
    · have hUCompIsfaIsBot : Uᶜ = {ϕ | ϕ a = ⊥} := by {
        rw [@Set.Subset.antisymm_iff]
        constructor
        · intro ϕ hphiInUcomp
          rw [@Set.mem_setOf_eq]
          have hphiANeqTop : ϕ a ≠ ⊤ := by {
            subst h
            simp_all only [Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq, not_false_eq_true]
          }
          exact not_bot_lt_iff.mp hphiANeqTop
        · intro ϕ h
          rw [@Set.mem_compl_iff]
          subst U
          rw [@Set.notMem_setOf_iff]
          simp [Set.mem_setOf_eq] at h
          rw [h]
          exact LT.lt.ne_top rfl
      }
      have hUCompIsClosed : IsClosed Uᶜ := by {
        rw [hUCompIsfaIsBot]
        exact fa_is_b_set_is_closed
      }
      exact isClosed_compl_iff.mp hUCompIsClosed
}

lemma clopen_is_fa_is_top {A : BoolAlg} {U : Set (TopCat.of (A ⟶ Two))} (hUIsClopen : IsClopen U) :
  ∃! a : A, U = {ϕ | ϕ a = ⊤} := by {
    sorry
}

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

def StoneIsomorphism (A : BoolAlg) : ((𝟭 BoolAlg).obj A) ⟶ ((Hom2 ⋙ Clop).obj A) := by {
  let g : BoundedLatticeHom ((𝟭 BoolAlg).obj A) ((Hom2 ⋙ Clop).obj A) := by refine {
    toFun := by {
      intro a
      have UIsfaTop : ∃ b, {ϕ : A ⟶ Two| ϕ a = ⊤} = {ϕ : A ⟶ Two| ϕ b = ⊤} :=
        by {exact Exists.intro a rfl}
      use {ϕ : A ⟶ Two| ϕ a = ⊤}
      exact fa_is_top_set_is_clopen UIsfaTop
    }
    map_sup' := by {
      intro a b
      apply TopologicalSpace.Clopens.ext
      apply Set.ext
      intro ϕ
      constructor
      · intro phiInfab
        simp_all only [Functor.id_obj, map_sup, max_eq_top,
          TopologicalSpace.Clopens.coe_mk, Functor.comp_obj, SetLike.mem_coe]
        exact phiInfab
      · intro a_1
        simp_all only [Functor.comp_obj, SetLike.mem_coe, Functor.id_obj, map_sup, max_eq_top,
          TopologicalSpace.Clopens.coe_mk]
        exact a_1
    }
    map_inf' := by {
      intro a b
      apply TopologicalSpace.Clopens.ext
      apply Set.ext
      intro ϕ
      constructor
      · intro a_1
        simp_all only [Functor.id_obj, map_inf, inf_eq_top_iff,
          TopologicalSpace.Clopens.coe_mk, Functor.comp_obj, SetLike.mem_coe]
        exact a_1
      · intro a_1
        simp_all only [Functor.comp_obj, SetLike.mem_coe, Functor.id_obj, map_inf,
          inf_eq_top_iff, TopologicalSpace.Clopens.coe_mk]
        exact a_1
    }
    map_top' := by {
      simp_all only [Functor.comp_obj, Functor.id_obj, map_top]
      rfl
    }
    map_bot' := by {
      simp_all only [Functor.comp_obj, Functor.id_obj, map_bot]
      apply TopologicalSpace.Clopens.ext
      simp_all only [TopologicalSpace.Clopens.coe_mk]
      change {ϕ | ⊥ = ⊤} = ∅
      suffices {ϕ | ⊥ = ⊤} ⊆ ∅ by {
        simp_all only [Set.subset_empty_iff]
        exact this
      }
      intro ϕ h
      suffices false by {
        simp_all only [Set.mem_setOf_eq, Bool.false_eq_true]
      }
      exact h
    }
  }
  use g
  · exact g.map_top'
  · exact g.map_bot'
}


def StoneIsomorphismInv (A : BoolAlg) : ((Hom2 ⋙ Clop).obj A) ⟶ ((𝟭 BoolAlg).obj A) := by {
  let g : BoundedLatticeHom ((Hom2 ⋙ Clop).obj A) ((𝟭 BoolAlg).obj A) := by refine {
    toFun := fun U => Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
    map_sup' := by {
      intro U V
      change TopologicalSpace.Clopens (A ⟶ Two) at U
      change TopologicalSpace.Clopens (A ⟶ Two) at V
      let a := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
      let b := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))
      let c := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊔ V)))
      have hUIsPhiaTop : (U : Set (TopCat.of (A ⟶ Two))) = {ϕ | ϕ a = ⊤} := by {
        exact (Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))).1
      }
      have hVIsPhibTop : (V : Set (TopCat.of (A ⟶ Two))) = {ϕ | ϕ b = ⊤} := by {
        exact (Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))).1
      }
      have hUsupVIsPhiaSupbTop : (U ⊔ V : Set (TopCat.of (A ⟶ Two))) = {ϕ | ϕ c = ⊤} := by {
        exact (Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊔ V)))).1
      }
      suffices (U ⊔ V : Set (TopCat.of (A ⟶ Two))) = {ϕ | ϕ (a ⊔ b) = ⊤} by {
        sorry
      }
      sorry
    }
    map_inf' := sorry
    map_top' := sorry
    map_bot' := sorry
  }
  use g
  · exact g.map_top'
  · exact g.map_bot'
}

def StoneRepresentationEquivalence : BoolAlg ≌ Profiniteᵒᵖ := by refine {
  functor := Hom2
  inverse := Clop
  unitIso := by refine {
    hom := by refine {
      app := fun A => StoneIsomorphism A
    }
    inv := by refine {
      app := fun A => StoneIsomorphismInv A
      naturality := sorry
    }
  }
  counitIso := by sorry
}
