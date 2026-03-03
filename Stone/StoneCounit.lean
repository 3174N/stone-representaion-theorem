import Stone.Defs

open CategoryTheory

noncomputable def basicHom {X : Profiniteᵒᵖ} (x : X.unop) : Clop.obj X ⟶ Two := by {
  let g : BoundedLatticeHom (Clop.obj X) Two := by classical refine {
    toFun := by {
      intro U
      change TopologicalSpace.Clopens X.unop at U
      exact if x ∈ U then ⊤ else ⊥
    }
    map_sup' := by {
      intro U V
      change TopologicalSpace.Clopens X.unop at U
      change TopologicalSpace.Clopens X.unop at V
      simp only [id_eq]
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
            simp_all only [TopologicalSpace.Clopens.coe_sup, SetLike.mem_coe, false_or]
        }
        simp_all only [↓reduceIte]
        rw [←h]
        simp [bot_le]
    }
    map_inf' := by {
      intro U V
      change TopologicalSpace.Clopens X.unop at U
      change TopologicalSpace.Clopens X.unop at V
      simp only [id_eq]
      let a := (if x ∈ U then (⊤ : Two) else (⊥ : Two))
      let b := (if x ∈ V then (⊤ : Two) else (⊥ : Two))
      let c := (if x ∈ U ⊓ V then (⊤ : Two) else (⊥ : Two))
      have h_x_in_or_nin : x ∈ U ∨ x ∉ U := by {
        exact Classical.em (x ∈ U)
      }
      rcases h_x_in_or_nin with h_x_in_U | h_x_nin_U
      · simp_all only [↓reduceIte]
        have h : x ∈ V ↔ x ∈ U ⊓ V := by {
          constructor
          · suffices x ∈ V → x ∈ (U : Set X.unop) ∩ (V : Set X.unop) by { exact this }
            intro h_x_in_V
            rw [@Set.mem_inter_iff]
            exact ⟨h_x_in_U, h_x_in_V⟩
          · suffices x ∈ (U : Set X.unop) ∩ (V : Set X.unop) → x ∈ V by { exact this }
            intro a_1
            simp_all only [Set.mem_inter_iff, SetLike.mem_coe, true_and]
        }
        rw [h]
        exact rfl
      · have h : x ∉ U ⊓ V := by {
          rw [←SetLike.mem_coe]
          simp_all only [TopologicalSpace.Clopens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
            false_and, not_false_eq_true]
        }
        simp_all only [↓reduceIte]
        rfl
    }
    map_top' := by {
      simp_all only [id_eq, ite_eq_left_iff, bot_ne_top, imp_false, Decidable.not_not]
      exact trivial
    }
    map_bot' := by {
      simp_all only [id_eq, ite_eq_right_iff, top_ne_bot, imp_false]
      apply Aesop.BuiltinRules.not_intro
      intro a
      exact a
    }
  }
  use g
  · exact map_top g
  · exact map_bot g
}

lemma basic_hom_apply_in {X : Profiniteᵒᵖ} {x : X.unop} {V : TopologicalSpace.Clopens X.unop} :
x ∈ V ↔ (basicHom x) V = ⊤ := by {
  classical
  change x ∈ V ↔ ((if x ∈ V then (⊤ : Two) else ⊥) = ⊤)
  constructor
  · intro hx
    simp [hx]
  · intro h
    simp_all only [ite_eq_left_iff, bot_ne_top, imp_false, Decidable.not_not]
}

lemma two_ne_bot_eq_top {a : Two} : a ≠ ⊥ ↔ a = ⊤ := by {
  constructor
  · intro h
    cases a
    · contradiction
    · rfl
  · intro h hbot
    rw [h] at hbot
    exact top_ne_bot hbot
}

lemma hom_basic_hom_existence {X : Profiniteᵒᵖ} (ϕ : (Clop.obj X) ⟶ Two) :
∃(x : X.unop), ϕ = basicHom x := by {
  let F : Filter X.unop := by refine {
    sets := { V | ∃(U : TopologicalSpace.Clopens X.unop), ( (U : Set _) ⊆ V ∧ ϕ U = ⊤) }
    univ_sets := by {
      rw [Set.mem_setOf]
      use ⊤
      constructor
      · exact fun ⦃a⦄ a_1 ↦ a_1
      · exact map_top (ConcreteCategory.hom ϕ)
    }
    sets_of_superset := by {
      intro A B h1 h2
      rw [Set.mem_setOf]
      rw [Set.mem_setOf] at h1
      obtain ⟨U, h3⟩ := h1
      use U
      constructor
      · apply subset_trans
        · exact h3.1
        · exact h2
      · exact h3.2
    }
    inter_sets := by {
      intro A B h_A_in h_B_in
      rw [Set.mem_setOf]
      obtain ⟨U, h_U_A⟩ := h_A_in
      obtain ⟨V, h_V_B⟩ := h_B_in
      use U ⊓ V
      constructor
      · simp
        constructor
        · intro x h
          rw [Set.mem_inter_iff] at h
          apply h_U_A.1
          exact h.1
        · intro x h
          rw [Set.mem_inter_iff] at h
          apply h_V_B.1
          exact h.2
      · suffices ϕ (U ⊓ V) = ⊤ by {exact this}
        rw [map_inf (ConcreteCategory.hom ϕ)]
        simp_all only [min_self]
    }
  }
  have h_F_ne_bot : F.NeBot := by {
    rw [@Filter.neBot_iff]
    change ¬(F = ⊥)
    rw [Filter.ext_iff]
    rw [@not_forall]
    use ∅
    have h_e_in_bot : ∅ ∈ (⊥ : Filter X.unop) := by {
      simp_all only [Filter.mem_bot]
    }
    have h_e_nin_F : ¬ ∅ ∈ F := by {
      unfold F
      simp
      intro V h
      have h_V_is_bot : V = ⊥ := by {
        exact TopologicalSpace.Clopens.ext h
      }
      rw [h_V_is_bot]
      subst h_V_is_bot
      simp_all only [Filter.mem_bot, TopologicalSpace.Clopens.coe_bot, map_bot,
        bot_ne_top, not_false_eq_true]
    }
    simp_all only [Filter.mem_bot, Filter.mem_mk, Set.mem_setOf_eq, Set.subset_empty_iff,
    not_exists, not_and, iff_true, not_false_eq_true, implies_true, F]
  }
  have h_x_exists : ∃ x ∈ Set.univ, ClusterPt x F := by {
    apply X.unop.is_compact.isCompact_univ
    simp_all only [Filter.principal_univ, le_top, F]
  }
  obtain ⟨x, h_x_cluster_pt_F⟩ := h_x_exists
  use x
  rw [BoolAlg.hom_ext_iff]
  apply BoundedLatticeHom.ext
  intro V
  change TopologicalSpace.Clopens X.unop at V
  have h_x_in_or_nin : x ∈ V ∨ x ∉ V := by {
    exact Classical.em (x ∈ V)
  }
  rcases h_x_in_or_nin with h_x_in_V | h_x_nin_V
  · simp_all
    have h_V_nhbr_x : (V : Set _) ∈ nhds x := by {
      exact V.isOpen.mem_nhds h_x_in_V
    }
    rw [basic_hom_apply_in.1 h_x_in_V]
    by_contra!
    have h_phi_V_bot : ϕ V = ⊥ := by {
      suffices (BoolAlg.Hom.hom ϕ) V = ⊥ by {
        exact this
      }
      simp_all only [ne_eq, F]
      exact not_bot_lt_iff.mp this
    }
    have h_phi_Vc_top : ϕ (Vᶜ) = ⊤ := by {
      simp_all only [ne_eq, map_compl, compl_bot, F]
    }
    have h_Vc_in_F : (Vᶜ : Set _) ∈ F := by {
      unfold F
      simp
      use Vᶜ
      constructor
      · exact fun ⦃a⦄ a_1 ↦ a_1
      · exact h_phi_Vc_top
    }
    have h_inf_bot : ((nhds x) ⊓ F) = ⊥ := by {
      rw [Filter.inf_eq_bot_iff]
      use V
      constructor
      · exact h_V_nhbr_x
      · use Vᶜ
        constructor
        · exact h_Vc_in_F
        · simp_all only [ne_eq, map_compl, compl_bot, Filter.mem_mk,
          Set.mem_setOf_eq, Set.inter_compl_self, F]
    }
    have h_inf_ne_bot : ((nhds x) ⊓ F) ≠ ⊥ := by {
      unfold ClusterPt at h_x_cluster_pt_F
      rw [←Filter.neBot_iff]
      exact h_x_cluster_pt_F
    }
    simp_all only [ne_eq, map_compl, compl_bot, Filter.mem_mk, Set.mem_setOf_eq, F]
  · simp_all
    have h_x_in_Vc : x ∈ Vᶜ := by {exact h_x_nin_V}
    have h_Vc_nhbr_x : (Vᶜ : Set _) ∈ nhds x := by {
      exact (Vᶜ).isOpen.mem_nhds h_x_in_Vc
    }
    by_contra!
    have h_basic_x_V_bot : (basicHom x) V = ⊥ := by {
      suffices ¬ (basicHom x) V = ⊤ by {
        exact not_bot_lt_iff.mp this
      }
      rw [←basic_hom_apply_in]
      exact h_x_nin_V
    }
    have h_phi_V_top : ϕ V = ⊤ := by {
      rw [h_basic_x_V_bot] at this
      rw [two_ne_bot_eq_top] at this
      exact this
    }
    have h_V_in_F : (V : Set _) ∈ F := by {
      unfold F
      simp
      use V
    }
    have h_inf_bot : ((nhds x) ⊓ F) = ⊥ := by {
      rw [Filter.inf_eq_bot_iff]
      use Vᶜ
      constructor
      · exact h_Vc_nhbr_x
      · use V
        constructor
        · exact h_V_in_F
        · simp_all only [ne_eq, top_ne_bot, not_false_eq_true, Filter.mem_mk,
          Set.mem_setOf_eq, SetLike.coe_subset_coe, Set.compl_inter_self, F]
    }
    have h_inf_ne_bot : ((nhds x) ⊓ F) ≠ ⊥ := by {
      unfold ClusterPt at h_x_cluster_pt_F
      rw [←Filter.neBot_iff]
      exact h_x_cluster_pt_F
    }
    simp_all only [ne_eq, Filter.mem_mk, Set.mem_setOf_eq, F]
}

lemma hom_basic_hom_uniqueness {X : Profiniteᵒᵖ} {x y : X.unop} :
basicHom x = basicHom y → x = y := by {
  intro h_bx_e_by
  by_contra!
  obtain ⟨U, h_U_clopen, h_x_in_U, h_y_in_Uc⟩ := exists_isClopen_of_totally_separated this
  let V : TopologicalSpace.Clopens X.unop := ⟨U, h_U_clopen⟩
  suffices (basicHom x) V ≠ (basicHom y) V by {
    simp_all only [ne_eq, Set.mem_compl_iff, not_true_eq_false, V]
  }
  have : x ∈ V := by {exact h_x_in_U}
  have : y ∉ V := by {exact h_y_in_Uc}
  classical
  change (if x ∈ V then ⊤ else ⊥) ≠ (if y ∈ V then ⊤ else ⊥)
  simp_all
}

lemma hom_basic_hom {X : Profiniteᵒᵖ} (ϕ : (Clop.obj X) ⟶ Two) :
∃!(x : X.unop), ϕ = basicHom x := by {
  obtain ⟨x, h⟩ := hom_basic_hom_existence ϕ
  use x
  constructor
  · simp_all
  · intro y
    simp
    rw [h]
    intro h
    apply hom_basic_hom_uniqueness
    apply Eq.symm
    exact h
}

noncomputable def StoneCoIsomorphism_asCont (X : Profiniteᵒᵖ) :
ContinuousMap ((𝟭 Profiniteᵒᵖ).obj X).unop ((Clop ⋙ Hom2).obj X).unop := by {
  classical
  let g : ContinuousMap ((𝟭 Profiniteᵒᵖ).obj X).unop ((Clop ⋙ Hom2).obj X).unop := by refine {
    toFun := by {
      intro x
      let ϕ := basicHom x
      use (BoolAlg.Hom.hom ϕ).toLatticeHom
      · exact (BoolAlg.Hom.hom ϕ).map_top'
      · exact (BoolAlg.Hom.hom ϕ).map_bot'
    }
    continuous_toFun := by {
      rw [TopologicalSpace.IsTopologicalBasis.continuous_iff basis_of_stone_space]
      intro U h
      obtain ⟨V, h_U_is_basic_V⟩ := h
      change TopologicalSpace.Clopens X.unop.toTop at V
      set W := _
      change IsOpen W
      have h2 : V.carrier = W := by {
        apply Set.ext
        intro x
        constructor
        · intro h_x_in_V
          suffices (basicHom x) ∈ U by { exact this }
          subst U
          unfold basicSet
          rw [@Set.mem_setOf_eq]
          change (if x ∈ V then ⊤ else ⊥) = ⊤
          simp_all
          exact h_x_in_V
        · intro h_x_in_W
          have h_basic_x_in_basic_V : (basicHom x) ∈ U := h_x_in_W
          rw [←h_U_is_basic_V] at h_basic_x_in_basic_V
          have h_basic_x_V_top : (basicHom x) V = ⊤ := h_basic_x_in_basic_V
          by_contra!
          have h_basic_x_V_bot : (basicHom x) V = ⊥ := by {
            simp
            change (if x ∈ V then ⊤ else ⊥) = ⊥
            simp_all
            exact this
          }
          subst h_U_is_basic_V
          simp_all
      }
      rw [←h2]
      exact V.isOpen
    }
  }
  use g
  exact g.continuous
}

lemma stone_co_bijective {X : Profiniteᵒᵖ} :
Function.Bijective (StoneCoIsomorphism_asCont X) := by {
  simp_all
  rw [@Function.bijective_iff_existsUnique]
  unfold StoneCoIsomorphism_asCont
  intro ϕ
  change Clop.obj X ⟶ Two at ϕ
  obtain ⟨x, hl, h_x_unique⟩ := hom_basic_hom (ϕ)
  use x
  constructor
  · simp
    change basicHom x = ϕ
    apply Eq.symm
    exact hl
  · intro y h
    apply h_x_unique
    apply Eq.symm
    exact h
}

noncomputable def StoneCoIsomorphism (X : Profiniteᵒᵖ) :
((Clop ⋙ Hom2).obj X) ≅ ((𝟭 Profiniteᵒᵖ).obj X)
:= by {
  let e : ((𝟭 Profiniteᵒᵖ).obj X).unop ≃ ((Clop ⋙ Hom2).obj X).unop :=
    Equiv.ofBijective (StoneCoIsomorphism_asCont X) stone_co_bijective
  have he : Continuous e :=
    (StoneCoIsomorphism_asCont X).continuous
  let h : ((𝟭 Profiniteᵒᵖ).obj X).unop ≃ₜ ((Clop ⋙ Hom2).obj X).unop :=
    (he.homeoOfEquivCompactToT2 : ((𝟭 Profiniteᵒᵖ).obj X).unop ≃ₜ ((Clop ⋙ Hom2).obj X).unop)
  exact (CompHausLike.isoOfHomeo (h)).op
}

lemma clop_hom_f_of_basic_hom {X Y : Profiniteᵒᵖ} {f : X ⟶ Y} {y : Y.unop} :
((Clop ⋙ Hom2).map f).unop (basicHom (y)) = basicHom (f.unop y) := by {
  classical
  apply BoolAlg.ext
  intro U
  change TopologicalSpace.Clopens X.unop at U
  change
    (if y ∈ ((show TopologicalSpace.Clopens Y.unop from
        (ConcreteCategory.hom (Clop.map f)) U) : Set Y.unop) then (⊤ : Two) else ⊥)
      =
    (if f.unop y ∈ (U : Set X.unop) then (⊤ : Two) else ⊥)
  simp_all
  rfl
}

lemma StoneCoIsomorphism_inv_unop_basicHom {Z : Profiniteᵒᵖ} {z : Z.unop} :
((StoneCoIsomorphism Z).inv.unop) (basicHom z) = z := by {
  classical
  simp [StoneCoIsomorphism, CompHausLike.isoOfHomeo]
  have hz : (StoneCoIsomorphism Z).unop.hom z = basicHom z := by {
    classical
    change
      (Equiv.ofBijective (StoneCoIsomorphism_asCont Z) stone_co_bijective z) = basicHom z
    simp [Equiv.ofBijective, StoneCoIsomorphism_asCont]
    apply BoolAlg.hom_ext
    ext U
    rfl
  }
  change (StoneCoIsomorphism Z).unop.inv (basicHom z) = z
  rw [←hz]
  exact Iso.hom_inv_id_apply (StoneCoIsomorphism Z).unop z
}

noncomputable def StoneCounit : Clop ⋙ Hom2 ≅ 𝟭 Profiniteᵒᵖ := by refine {
  hom := by refine {
    app := fun X => (StoneCoIsomorphism X).hom
  }
  inv := by refine {
    app := fun X => (StoneCoIsomorphism X).inv
    naturality := by {
      intro X Y f
      apply Quiver.Hom.unop_inj
      ext ϕ
      change (Clop.obj Y ⟶ Two) at ϕ
      obtain ⟨y, rfl⟩ := hom_basic_hom_existence (X := Y) ϕ
      change (f.unop) ((StoneCoIsomorphism Y).inv.unop (basicHom y)) =
        (StoneCoIsomorphism X).inv.unop ((Hom2.map (Clop.map f)).unop (basicHom y))
      rw [StoneCoIsomorphism_inv_unop_basicHom (Z := Y) (z := y)]
      change (ConcreteCategory.hom f.unop) y =
        (ConcreteCategory.hom (StoneCoIsomorphism X).inv.unop)
          ((ConcreteCategory.hom (Hom2.map (Clop.map f)).unop) (basicHom y))

      have hmap : (ConcreteCategory.hom (Hom2.map (Clop.map f)).unop) (basicHom y)
        = basicHom ((ConcreteCategory.hom f.unop) y) := by {
        simpa using (clop_hom_f_of_basic_hom (f := f) (y := y))
      }
      have hinv (z : X.unop) :
      (ConcreteCategory.hom (StoneCoIsomorphism X).inv.unop) (basicHom z) = z := by {
        simpa using (StoneCoIsomorphism_inv_unop_basicHom (Z := X) (z := z))
      }
      rw [hmap, hinv ((ConcreteCategory.hom f.unop) y)]
    }
  }
}
