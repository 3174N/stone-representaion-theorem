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
import Stone.Defs

open CategoryTheory

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
    have := TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'
            basis_of_stone_space (IsClopen.isOpen hUIsClopen)
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

lemma sup_basics_basic_sup {A : BoolAlg} {a b : A} :
  basicSet a ⊔ basicSet b = basicSet (a ⊔ b) := by {
    unfold basicSet
    simp only [Set.sup_eq_union, map_sup, max_eq_top]
    apply Set.ext
    intro ϕ
    constructor
    · exact fun a ↦ a
    · exact fun a ↦ a
  }

lemma inf_basics_basic_inf {A : BoolAlg} {a b : A} :
  basicSet a ⊓ basicSet b = basicSet (a ⊓ b) := by {
  unfold basicSet
  simp only [Set.inf_eq_inter, map_inf, inf_eq_top_iff]
  apply Set.ext
  intro ϕ
  constructor
  · exact fun a ↦ a
  · exact fun a ↦ a
}

lemma basic_top_eq_top {A : BoolAlg} : basicSet (⊤ : A) = ⊤ := by {
  unfold basicSet
  simp only [map_top, Set.setOf_true, Set.top_eq_univ]
}

lemma basic_bot_eq_bot {A : BoolAlg} : basicSet (⊥ : A) = ⊥ := by {
  unfold basicSet
  simp only [map_bot, bot_ne_top, Set.setOf_false, Set.bot_eq_empty]
}

lemma clopen_basic_clopen {A : BoolAlg} (U : TopologicalSpace.Clopens (A ⟶ Two)) :
∃!a, U = basicClopen a := by {
  unfold basicClopen
  suffices ∃!a, U.carrier = basicSet a by {
    obtain ⟨ a, ha ⟩ := this
    unfold basicSet at ha
    use a
    dsimp
    dsimp at ha
    apply And.intro

    · have : U.carrier = { φ | (ConcreteCategory.hom φ) a = ⊤ } := ha.left
      exact TopologicalSpace.Clopens.ext this
    · intro y hy
      have : U.carrier = { φ | (ConcreteCategory.hom φ) y = ⊤ } := by {
        subst hy
        simp_all only
      }
      exact ha.right y this
  }
  exact clopen_is_fa_is_top U.isClopen'
}

lemma basic_set_clop_hom_map {A B : BoolAlg} {f : A ⟶ B} {a : A} :
((Hom2 ⋙ Clop).map f) (basicClopen a) = basicClopen (f a) := by {
  apply TopologicalSpace.Clopens.ext
  apply Set.ext
  intro φ
  apply Set.mem_setOf
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

noncomputable def StoneUnit : 𝟭 BoolAlg ≅ Hom2 ⋙ Clop := by refine {
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
      subst h_U_basic_phi
      simp_all only [Functor.id_obj, Functor.id_map]
    }
  }
  hom_inv_id := by {sorry}
  inv_hom_id := by {sorry}
}
