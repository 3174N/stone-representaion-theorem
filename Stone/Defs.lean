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
import Mathlib.Order.SymmDiff
import Mathlib.Topology.ContinuousMap.Defs

open CategoryTheory

def Two : BoolAlg := BoolAlg.of Bool
instance : TopologicalSpace Two := ⊥
instance : DiscreteTopology Two := ⟨rfl⟩
instance : ContinuousInf Two := ⟨continuous_of_discreteTopology⟩
instance : ContinuousSup Two := ⟨continuous_of_discreteTopology⟩
instance : Finite Two := Finite.of_fintype Bool
instance : T2Space Two := DiscreteTopology.toT2Space
noncomputable instance : LinearOrder Two := {
  le_total := by {
    intro a b
    cases a
    · left
      exact left_eq_inf.mp rfl
    · right
      exact congrFun rfl
  }
  toDecidableLE := Classical.decRel LE.le
  min_def := by {
    intro a b
    split
    next h => simp_all only [inf_of_le_left]
    next h =>
      simp_all only [not_le, inf_eq_right]
      exact Std.le_of_lt h
  }
  max_def := by {
    intro a b
    split
    next h => simp_all only [sup_of_le_right]
    next h =>
      simp_all only [not_le, sup_eq_left]
      exact Std.le_of_lt h
  }
}
instance : Nontrivial Two := by {
  rw [@nontrivial_iff_lt]
  use ⊥
  use ⊤
  rfl
}

def stoneEmbed (A : BoolAlg) : (A ⟶ Two) → (A → Bool) := fun f a => f a
instance {A : BoolAlg} : TopologicalSpace (A ⟶ Two) :=
  TopologicalSpace.induced (stoneEmbed A) inferInstance

instance {A : BoolAlg} : CompactSpace (A ⟶ Two) := by {
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

instance {A : BoolAlg} : T2Space (A ⟶ Two) := by {
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

instance {A : BoolAlg} : TotallyDisconnectedSpace (A ⟶ Two) := by {
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

def basicSet {A : BoolAlg} (a : A) : Set (TopCat.of (A ⟶ Two)) := {φ | φ a = ⊤}

def Clop : Profiniteᵒᵖ ⥤ BoolAlg := {
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
  obj := fun A => ⟨TopCat.of (A ⟶ Two), instTotallyDisconnectedSpaceHomBoolAlgTwo⟩
  map := by {
    intro A B f
    let HomA2 := TopCat.of (A ⟶ Two)
    let HomB2 :=  TopCat.of (B ⟶ Two)
    use fun ϕ ↦ (f ≫ ϕ)
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    exact (continuous_apply (f a)).comp continuous_induced_dom
  }
}

lemma fa_is_b_set_is_closed {A : BoolAlg} {a : A} {b : Two} :
IsClosed {ϕ : TopCat.of (A ⟶ Two) | ϕ a = b} := by {
  let U := {ϕ : TopCat.of (A ⟶ Two) | ϕ a = b}
  let PiA := fun (p : A ⟶ Two) => p a
  have ContPiA : Continuous PiA := by exact (continuous_apply a).comp continuous_induced_dom
  have UIsPreImOfbByProjA : U = PiA⁻¹' {b} := rfl
  have hSingletonIsClosed : IsClosed {b} := isClosed_singleton
  exact IsClosed.preimage ContPiA hSingletonIsClosed
}

lemma fa_is_top_set_is_clopen {A : BoolAlg} {U : Set (TopCat.of (A ⟶ Two))}
  (hUIsSetOfFaT : ∃ a : A, U = basicSet a) : IsClopen U := by {
    unfold basicSet at hUIsSetOfFaT
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

lemma basis_of_stone_space {A : BoolAlg} :
  TopologicalSpace.IsTopologicalBasis (Set.range (fun p : A => basicSet p)) := by {
  constructor
  · intro u₁ hu₁ u₂ hu₂ x hx
    obtain ⟨p, rfl⟩ := hu₁
    obtain ⟨q, rfl⟩ := hu₂
    use basicSet (p ⊓ q)
    constructor
    · exact ⟨p ⊓ q, rfl⟩
    · constructor
      · simp only [basicSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hx ⊢
        rw [map_inf]
        simp only [hx]
        rfl
      · intro φ hφ
        simp only [basicSet, Set.mem_setOf_eq] at hφ ⊢
        rw [map_inf] at hφ
        rw [inf_eq_top_iff] at hφ
        exact hφ
  · rw [Set.sUnion_range]
    refine Set.eq_univ_of_forall (fun φ => ?_)
    use basicSet ⊤
    constructor
    · exact ⟨⊤, rfl⟩
    · simp only [basicSet, Set.mem_setOf_eq, map_top]
  · apply le_antisymm
    · refine le_generateFrom ?_
      intro s hs
      rw [Set.mem_range] at hs
      obtain ⟨w, h⟩ := hs
      subst h
      have : IsClopen (basicSet w) := by {
        have : ∃ (a : A), basicSet w = basicSet a := by use w
        exact fa_is_top_set_is_clopen this
      }
      exact IsClopen.isOpen this
    · rw [instTopologicalSpaceHomBoolAlgTwo]
      refine continuous_iff_le_induced.mp ?_
      unfold stoneEmbed
      rw [@continuous_pi_iff]
      intro i
      rw [@continuous_discrete_rng]
      intro b
      cases b
      · have : false = ⊥ := rfl
        rw [this]
        have h_false : (fun a => (ConcreteCategory.hom a) i) ⁻¹' {⊥} = basicSet (iᶜ) := by {
          ext a
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, basicSet]
          constructor
          · intro hiBot
            rw [map_compl]
            exact compl_eq_top.mpr hiBot
          · intro hiCBot
            rw [map_compl] at hiCBot
            exact le_compl_self.mp fun a ↦ hiCBot
        }
        rw [h_false]
        apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact ⟨iᶜ, rfl⟩
      · have : true = ⊤ := rfl
        rw [this]
        have h_true : (fun a => (ConcreteCategory.hom a) i) ⁻¹' {⊤} = basicSet i := by {
          ext a
          simp [basicSet]
        }
        rw [h_true]
        apply TopologicalSpace.isOpen_generateFrom_of_mem
        exact ⟨i, rfl⟩
}

def basicClopen {A : BoolAlg} (a : A) : TopologicalSpace.Clopens (A ⟶ Two) := by {
  use {φ | φ a = ⊤}
  apply fa_is_top_set_is_clopen
  use a
  rfl
}
