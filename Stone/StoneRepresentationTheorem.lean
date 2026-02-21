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
import Stone.ExistsNonZeroHomomorphism

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

def basicSet {A : BoolAlg} (a : A) : Set (TopCat.of (A ⟶ Two)) :=
  {φ | φ a = ⊤}
-- def stoneSubbasis (A : BoolAlg) : Set (Set (TopCat.of (A ⟶ Two))) :=
--   {U | ∃ a : A, U = {ϕ : TopCat.of (A ⟶ Two) | ϕ a = ⊤}}

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

lemma projection_is_continuous {A : BoolAlg} {a : A} :
Continuous fun (p : A ⟶ Two) => p a := by {sorry}

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

lemma diffs_bot_a_eq_b {A : BoolAlg} {a b : A} (h_diffs_are_bot : a \ b = ⊥ ∧ b \ a = ⊥) : a = b
:= by {
  have h_a_sdiff_b_neq_bot : symmDiff a b = ⊥ := by {
    simp_all only [sdiff_eq_bot_iff, symmDiff_eq_bot]
    obtain ⟨ h_a_leq_b, h_b_leq_a ⟩ := h_diffs_are_bot
    apply le_antisymm
    · exact h_a_leq_b
    · exact h_b_leq_a
  }
  rw [←symmDiff_eq_bot]
  exact h_a_sdiff_b_neq_bot
}

lemma a_neq_b_diff_neq_bot {A : BoolAlg} {a b : A} (h_a_neq_b : a ≠ b) : a \ b ≠ ⊥ ∨ b \ a ≠ ⊥
:= by{
  by_contra!
  have h_a_eq_b : a = b := diffs_bot_a_eq_b this
  subst h_a_eq_b
  simp_all [ne_eq, not_true_eq_false]
}

lemma a_diff_b_neq_bot_exist {A : BoolAlg} {a b : A} (h_a_diff_b_neq_bot : a \ b ≠ ⊥) :
  ∃ (ϕ : A ⟶ Two), ϕ a = ⊤ ∧ ϕ b = ⊥ := by {
    obtain ⟨ϕ, h⟩ := (nonzero_homomorphism A Two (a \ b) h_a_diff_b_neq_bot)
    use ϕ
    have h_phi_ab : (ϕ a) ⊓ (ϕ (bᶜ)) = ⊤ := by {
      rw [Eq.symm (LatticeHomClass.map_inf (ConcreteCategory.hom ϕ) a bᶜ)]
      rw [← BooleanAlgebra.sdiff_eq a b]
      exact h
    }
    rw [inf_eq_top_iff] at h_phi_ab
    simp_all only [ne_eq, sdiff_eq_bot_iff, map_sdiff, top_sdiff',
      hnot_eq_compl, compl_eq_top, map_compl, compl_bot, and_true]
  }

lemma a_diff_b_ne_bot_ne {A : BoolAlg} {a b : A} (h_a_diff_b_ne_bot : a \ b ≠ ⊥) :
  {φ : A ⟶ Two | φ a = ⊤} ≠ {φ : A ⟶ Two | φ b = ⊤} := by {
    obtain ⟨ϕ, h_phi_a_top, h_phi_b_bot⟩ := a_diff_b_neq_bot_exist h_a_diff_b_ne_bot
    have h_phi_in_a_top : ϕ ∈ {φ | φ a = ⊤} := h_phi_a_top
    have h_phi_not_in_b_top : ϕ ∉ {φ | φ b = ⊤} := by {
      by_contra!
      have h_phi_b_top : ϕ b = ⊤ := this
      have h_bot_phi_b : ⊥ = ϕ b := by {
        apply Eq.symm
        exact h_phi_b_bot
      }
      have h_bot_is_top : ⊥ = ⊤ := by {
        exact Eq.trans h_bot_phi_b h_phi_b_top
      }
      exact bot_ne_top h_bot_is_top
    }
    exact ne_of_mem_of_not_mem' h_phi_a_top h_phi_not_in_b_top
  }

lemma clopen_is_fa_is_top {A : BoolAlg} {U : Set (TopCat.of (A ⟶ Two))} (hUIsClopen : IsClopen U) :
  ∃! a : A, U = basicSet a := by {
  have hUIsCompact : IsCompact U := by {
    have hUIsClosed : IsClosed U := IsClopen.isClosed hUIsClopen
    exact IsClosed.isCompact hUIsClosed
  }
  have hUUnionOfBasis : U = ⋃₀ {s | (∃ p, s = basicSet p) ∧ s ⊆ U} := by {
    have := TopologicalSpace.IsTopologicalBasis.open_eq_sUnion' basis_of_stone_space (IsClopen.isOpen hUIsClopen)
    grind only [= Set.subset_def, = Set.setOf_true, = Set.mem_range, = Set.mem_empty_iff_false,
      usr Set.mem_setOf_eq, = Set.setOf_false, = Set.mem_sUnion, ← Set.mem_univ, cases Or]
  }
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let ι : A → Set (TopCat.of (A ⟶ Two)) := fun p => basicSet p
    let valid_indices := { p : A | basicSet p ⊆ U }
    have h_cover : U ⊆ ⋃ p ∈ valid_indices, ι p := by
      rw [hUUnionOfBasis]
      intro x hx
      obtain ⟨s, ⟨⟨p, rfl⟩, hs_sub⟩, hxs⟩ := hx
      simp only [Set.mem_iUnion]
      use p
      constructor
      · exact hxs
      · exact hs_sub

    obtain ⟨t, ht_sub, htFinite, ht_cover⟩ := hUIsCompact.elim_finite_subcover_image
      (fun p _ => IsClopen.isOpen (fa_is_top_set_is_clopen ⟨p, rfl⟩))
      h_cover

    lift t to Finset A using htFinite

    use t.sup id
    apply Set.Subset.antisymm
    · refine Set.Subset.trans ht_cover ?_
      intro φ hφ
      simp only [Set.mem_iUnion, exists_prop] at hφ
      obtain ⟨p, hp, hφp⟩ := hφ
      simp only [basicSet, Set.mem_setOf_eq] at hφp ⊢
      have h_le : p ≤ t.sup id := Finset.le_sup (f := id) hp
      have h_sup_eq : p ⊔ t.sup id = t.sup id := by {
        rw [sup_comm]
        exact sup_of_le_left h_le
      }
      apply_fun φ at h_sup_eq
      rw [map_sup] at h_sup_eq
      rw [hφp] at h_sup_eq
      exact h_sup_eq.symm
    · simp only [basicSet]
      intro φ hφ
      change (ConcreteCategory.hom φ) (t.sup id) = ⊤ at hφ
      rw [map_finset_sup] at hφ
      simp at hφ
      rw [@Finset.sup_eq_top_iff] at hφ
      obtain ⟨p, hp_mem, hp_val⟩ := hφ
      have hp_subset : basicSet p ⊆ U := ht_sub hp_mem
      apply hp_subset
      exact hp_val
  · intro a b ha hb
    simp [basicSet] at ha hb
    rw [ha] at hb
    by_contra!
    have h_ab_neq_bot : a \ b ≠ ⊥ ∨ b \ a ≠ ⊥ := a_neq_b_diff_neq_bot this
    rcases h_ab_neq_bot with h_a_diff_b_neq_bot | h_b_diff_a_neq_bot
    · exact (a_diff_b_ne_bot_ne (h_a_diff_b_neq_bot)) hb
    · exact (a_diff_b_ne_bot_ne (h_b_diff_a_neq_bot)) (Eq.symm hb)
}

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
  obj := fun A => ⟨TopCat.of (A ⟶ Two), stone_space_is_totally_disconnected A⟩
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

lemma sup_basics_basic_sup {A : BoolAlg} {a b : A} :
  basicSet a ⊔ basicSet b = basicSet (a ⊔ b) := by {
    apply Set.ext
    intro ϕ
    constructor
    · sorry
    · sorry
  }

lemma inf_basics_basic_inf {A : BoolAlg} {a b : A} :
  basicSet a ⊓ basicSet b = basicSet (a ⊓ b) := by {
    sorry
  }

lemma basic_top_eq_top {A : BoolAlg} : basicSet (⊤ : A) = ⊤ := by {
  sorry
}

lemma basic_bot_eq_bot {A : BoolAlg} : basicSet (⊥ : A) = ⊥ := by {
  sorry
}

noncomputable def StoneIsomorphismInv (A : BoolAlg) :
((Hom2 ⋙ Clop).obj A) ⟶ ((𝟭 BoolAlg).obj A)
:= by {
  let g : BoundedLatticeHom ((Hom2 ⋙ Clop).obj A) ((𝟭 BoolAlg).obj A) := by refine {
    toFun := fun U => Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
    map_sup' := by {
      intro U V
      change TopologicalSpace.Clopens (A ⟶ Two) at U
      change TopologicalSpace.Clopens (A ⟶ Two) at V
      let a := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
      let b := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))
      let c := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊔ V)))
      suffices a ⊔ b = c by exact id (Eq.symm this)
      obtain h_a_is_unique_U :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
      obtain h_b_is_unique_V :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))
      obtain h_c_is_unique_U_sup_V :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊔ V)))
      apply h_c_is_unique_U_sup_V.2
      suffices ↑(↑(U)⊔ ↑(V)) = basicSet (a ⊔ b) by exact this
      rw [h_a_is_unique_U.1, h_b_is_unique_V.1]
      exact sup_basics_basic_sup
    }
    map_inf' := by {
      intro U V
      change TopologicalSpace.Clopens (A ⟶ Two) at U
      change TopologicalSpace.Clopens (A ⟶ Two) at V
      let a := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
      let b := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))
      let c := Classical.choose (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊓ V)))
      suffices a ⊓ b = c by exact id (Eq.symm this)
      obtain h_a_is_unique_U :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen U))
      obtain h_b_is_unique_V :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen V))
      obtain h_c_is_unique_U_inf_V :=
        Exists.choose_spec (clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (U ⊓ V)))
      apply h_c_is_unique_U_inf_V.2
      suffices ↑(↑(U) ⊓ ↑(V)) = basicSet (a ⊓ b) by exact this
      rw [h_a_is_unique_U.1, h_b_is_unique_V.1]
      exact inf_basics_basic_inf
    }
    map_top' := by {
      let a := Classical.choose (
          clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (⊤ : ((Hom2 ⋙ Clop).obj A)))
        )
      suffices a = ⊤ by exact this
      obtain h_a_is_unique_top :=
        Exists.choose_spec (
            clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (⊤ : ((Hom2 ⋙ Clop).obj A)))
          )
      apply Eq.symm
      apply h_a_is_unique_top.2
      apply Eq.symm
      exact basic_top_eq_top
    }
    map_bot' := by {
      let a := Classical.choose (
          clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (⊥ : ((Hom2 ⋙ Clop).obj A)))
        )
      suffices a = ⊥ by exact this
      obtain h_a_is_unique_bot :=
        Exists.choose_spec (
            clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (⊥ : ((Hom2 ⋙ Clop).obj A)))
          )
      apply Eq.symm
      apply h_a_is_unique_bot.2
      apply Eq.symm
      exact basic_bot_eq_bot
    }
  }
  use g
  · exact g.map_top'
  · exact g.map_bot'
}

noncomputable def StoneCoIsomorphism (X : Profiniteᵒᵖ) :
((Clop ⋙ Hom2).obj X) ⟶ ((𝟭 Profiniteᵒᵖ).obj X) := by {
  classical
  let g : ContinuousMap ((𝟭 Profiniteᵒᵖ).obj X).unop ((Clop ⋙ Hom2).obj X).unop := by refine {
    toFun := by {
      intro x
      let ϕ : BoundedLatticeHom (Clop.obj X) Two := by refine {
        toFun := by {
          intro U
          change TopologicalSpace.Clopens X.unop at U
          exact if x ∈ U then ⊤ else ⊥
        }
        map_sup' := by {
          intro U V
          change TopologicalSpace.Clopens X.unop at U
          change TopologicalSpace.Clopens X.unop at V
          simp only [Functor.id_obj, id_eq]
          let a := (if x ∈ U then (⊤ : Two) else (⊥ : Two))
          let b := (if x ∈ V then (⊤ : Two) else (⊥ : Two))
          let c := (if x ∈ U ⊔ V then (⊤ : Two) else (⊥ : Two))
          have h_x_in_or_nin : x ∈ U ∨ x ∉ U := by {
            exact Classical.em (x ∈ U)
          }
          rcases h_x_in_or_nin with h_x_in_U | h_x_nin_U
          · have h_x_in_U_sup_V : x ∈ U ⊔ V := by {
              apply Set.mem_union_left
              exact h_x_in_U
            }
            have h_c_eq_top : c = (⊤ : Two) := by {
              exact if_pos h_x_in_U_sup_V
            }
            have h_a_eq_top : a = (⊤ : Two) := by {
              exact if_pos h_x_in_U
            }
            simp_all only [↓reduceIte]
            simp [le_top]
          · have h_a_eq_bot : a = (⊥ : Two) := by {
              exact if_neg h_x_nin_U
            }
            have h : x ∈ V ↔ x ∈ U ⊔ V := by {
              constructor
              · apply Set.mem_union_right
              · have h_union_is_sup : (U : Set X.unop) ∪ (V : Set X.unop) = U ⊔ V := rfl
                suffices x ∈ (U : Set X.unop) ∪ (V : Set X.unop) → x ∈ V by exact this
                rw [Set.mem_union]
                intro h
                simp_all only [Functor.id_obj, TopologicalSpace.Clopens.coe_sup, SetLike.mem_coe, false_or]
            }
            simp_all only [↓reduceIte]
            rw [←h]
            simp [bot_le]
        }
        map_inf' := sorry
        map_top' := sorry
        map_bot' := sorry
      }
      use ϕ
      · exact ϕ.map_top'
      · exact ϕ.map_bot'
    }
    continuous_toFun := sorry
  }
  use g
  rw [@continuous_def]
  sorry
}

def StoneCoIsomorphismInv (X : Profiniteᵒᵖ) :
((𝟭 Profiniteᵒᵖ).obj X) ⟶ ((Clop ⋙ Hom2).obj X) := by {sorry}

def basicClopen {A : BoolAlg} (a : A) : TopologicalSpace.Clopens (A ⟶ Two) := by {
  use {φ | φ a = ⊤}
  apply fa_is_top_set_is_clopen
  use a
  rfl
}

lemma clopen_basic_clopen {A : BoolAlg} (U : TopologicalSpace.Clopens (A ⟶ Two)) :
∃!a, U = basicClopen a := by {sorry}

lemma basic_set_clop_hom_map {A B : BoolAlg} {f : A ⟶ B} {a : A} :
((Hom2 ⋙ Clop).map f) (basicClopen a) = basicClopen (f a) := by {
  apply TopologicalSpace.Clopens.ext
  apply Set.ext
  intro φ
  apply Set.mem_setOf
}

lemma basic_set_stone_inv_hom_map {A : BoolAlg} {a : A} :
(((StoneIsomorphismInv A)) (basicClopen a)) = a := by {
  let b := Classical.choose (
    clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (basicClopen a)))
  change b = a
  apply Eq.symm
  obtain ⟨_, hr⟩ := Classical.choose_spec (
    clopen_is_fa_is_top (TopologicalSpace.Clopens.isClopen (basicClopen a)))
  apply hr
  rfl
}

noncomputable def StoneRepresentationEquivalence : BoolAlg ≌ Profiniteᵒᵖ := by refine {
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
  counitIso := {
    hom := {
      app := fun X => StoneCoIsomorphism X
    }
    inv := {
      app := fun X => StoneCoIsomorphismInv X
      naturality := by {
        sorry
      }
    }
    hom_inv_id := by {sorry}
    inv_hom_id := by {sorry}
  }
}
