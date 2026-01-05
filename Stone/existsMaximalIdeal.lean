import Mathlib.Tactic
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Ideal
import Mathlib.Order.Zorn
import Mathlib.Topology.Category.Profinite.Basic

lemma exists_maximal_ideal (A : BoolAlg) (I : Order.Ideal A) (hIProper : I.IsProper)
  : ∃ I' : Order.Ideal A, I'.IsMaximal ∧ I ≤ I' := by
  {
    let s := { J : Order.Ideal A | I ≤ J ∧ J.IsProper}
    have hZornPremise :
    ∀ (c : Set s), IsChain (fun a b : s => a ≤ b) c → c.Nonempty → ∃ (ub : s), ∀ a ∈ c, a ≤ ub
    := by {
      intro c
      intro hcChain
      intro hCNonEmpty
      let K : Order.Ideal A := {
        carrier := { a : A | ∃ J ∈ c, a ∈ J.val}
        lower' := by {
          unfold IsLowerSet
          intro a b
          intro bLeqa
          intro aInUnion
          let ⟨Ja, hJaInc, haInJa⟩ := aInUnion
          use Ja
          constructor
          · exact hJaInc
          · exact Ja.val.lower bLeqa haInJa
        }
        nonempty' := by {
          unfold Set.Nonempty
          use ⊥
          change ∃J∈c, ⊥ ∈ J.val
          let ⟨J, hJInC⟩ := hCNonEmpty
          use J
          simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Order.Ideal.bot_mem, and_self, s]
        }
        directed' := by {
          unfold DirectedOn
          intro x hXInUnion
          intro y hYInUnion
          let ⟨Jx, hJxInC, hXInJx⟩ := hXInUnion
          let ⟨Jy, hJyInC, hYInJy⟩ := hYInUnion
          have hJxJyComparable : Jx ≤ Jy ∨ Jy ≤ Jx := by exact IsChain.total hcChain hJxInC hJyInC
          use x ⊔ y
          constructor
          case h.left =>
            rcases hJxJyComparable with JxLeqJy | JyLeqJx
            · have hXInJy : x ∈ Jy.val := by {
                apply JxLeqJy
                exact hXInJx
              }
              use Jy
              simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists,
              exists_and_right, Order.Ideal.sup_mem_iff, and_self, s]
            · have hYInJX : y ∈ Jx.val := by {
                apply JyLeqJx
                exact hYInJy
              }
              use Jx
              simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists,
              exists_and_right, Order.Ideal.sup_mem_iff, and_self, s]

          case h.right =>
            simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists,
            exists_and_right, le_sup_left, le_sup_right, and_self, s]
        }
      }
      have hIleqK : I ≤ K := by {
        let ⟨ J, hJInc ⟩ := hCNonEmpty
        intro x
        intro xInI
        use J
        constructor
        · exact hJInc
        · obtain ⟨Jval, hILeqJ, _ ⟩ := J
          apply hILeqJ
          exact xInI
      }
      have hKIsProper : K.IsProper := by {
        rw [Order.Ideal.isProper_iff]
        rw [Set.ne_univ_iff_exists_notMem]
        have hTopNinI : ⊤ ∉ K := by {
          change ¬ ∃ J ∈ c, ⊤ ∈ J.val
          simp only [not_exists, not_and]
          intro x _
          obtain ⟨_, _, JisProper⟩ := x
          exact Order.Ideal.IsProper.top_notMem JisProper
        }
        use ⊤
        exact hTopNinI
      }
      use ⟨K, ⟨hIleqK, hKIsProper⟩⟩
      intro a haInc
      intro x hxIna
      change ∃J∈ c, x∈ J.val
      use a
      exact ⟨haInc, hxIna⟩
    }
    have hIdealLeqIsTrans : ∀ {I J K : Order.Ideal A}, I ≤ J → J ≤ K → I ≤ K := by {
      intro I J K
      intro hILeqJ
      intro hJLeqK
      intro x
      intro hxInI
      apply hJLeqK
      apply hILeqJ
      exact hxInI
    }
    have : Nonempty s := by {
      use I
      simp [s]
      exact hIProper
    }
    have hMax : ∃ (I' : s), ∀ (J : s), I' ≤ J → J ≤ I' := by {
      exact exists_maximal_of_nonempty_chains_bounded hZornPremise hIdealLeqIsTrans
    }
    rcases hMax with ⟨M, hM⟩
    use M
    obtain ⟨Mval, hILeqM, hMIsProper⟩ := M
    constructor
    case left =>
      rw [@Order.Ideal.isMaximal_iff]
      constructor
      · exact hMIsProper
      · intro J hMLJ
        by_contra!
        have hJIsProper : J.IsProper := by {
          rw [J.isProper_iff]
          exact this
        }
        have hILeqJ : I ≤ J := by {
          suffices Mval ≤ J → I ≤ J by {
            apply this
            apply le_of_lt hMLJ
          }
          apply le_trans
          exact hILeqM
        }
        have hJInS : J ∈ s := by exact And.intro hILeqJ hJIsProper
        have hJLeqM : J ≤ Mval := by {
          apply hM ⟨J, hJInS⟩
          apply le_of_lt hMLJ
        }
        have hJNotLeqM : ¬ (J ≤ Mval) := by exact LT.lt.not_ge hMLJ
        exact hJNotLeqM hJLeqM
    case right =>
      simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, forall_and_index,
        Subtype.exists, Subtype.mk_le_mk, exists_prop, s]
  }

noncomputable def StoneRep : BoolAlg ≌ Profinite := by sorry
