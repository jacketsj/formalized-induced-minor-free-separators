import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLSetup
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLCore

/-!
# LLL Application: From Concurrent Flow to Induced Almost-Embedding
-/

open Finset SimpleGraph Real
open scoped BigOperators NNReal

noncomputable section

namespace SimpleGraph.LLLApp

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableRel G.Adj] in
lemma iae_of_no_edges (hH : H.edgeFinset = ∅) :
    Nonempty (InducedAlmostEmbedding G H) := by
  constructor; constructor
  all_goals simp_all +decide []
  · exact fun _ => Classical.arbitrary V
  · aesop

omit [Nonempty V] [DecidableRel G.Adj] in
lemma cf_support_nonempty (cf : ConcurrentFlow G) (hV : 2 ≤ Fintype.card V) :
    cf.support.Nonempty := by
  obtain ⟨s, t, hst⟩ : ∃ s t : V, s ≠ t := by
    exact Fintype.one_lt_card_iff.1 hV;
  have := cf.total_flow s t hst;
  contrapose! this; aesop;

omit [Nonempty V] [DecidableRel G.Adj] in
lemma exists_path_for_pair (cf : ConcurrentFlow G) (s t : V) (hst : s ≠ t) :
    ∃ l ∈ cf.support, l.head? = some s ∧ l.getLast? = some t := by
  contrapose! hst; simp_all +decide [  ] ;
  convert cf.total_flow s t;
  rw [ Finset.sum_eq_zero ] <;> aesop

/-- The core LLL theorem: existence of φ and pathChoice satisfying all conditions.
    This is Lemma 4.3 from [KL24]. -/
private theorem lll_good_assignment_core
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 0 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  by_cases hVsmall : Fintype.card V ≤ 3
  · exact (small_V_vacuous cf hcong hEH hV hVsmall).elim
  · push_neg at hVsmall
    exact SimpleGraph.LLLCore.exists_good_assignment hH cf hcong hEH hV hVsmall

theorem lll_good_assignment_exists
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 0 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  exact lll_good_assignment_core hH cf hcong hEH hV

omit [Fintype V] [Nonempty V] [DecidableRel G.Adj] in
lemma mutuallyInducedPaths_reverse_left (l₁ l₂ : List V) :
    MutuallyInducedPaths G l₁.reverse l₂ ↔ MutuallyInducedPaths G l₁ l₂ := by
  simp +decide [ MutuallyInducedPaths ]

omit [Fintype V] [Nonempty V] [DecidableRel G.Adj] in
lemma mutuallyInducedPaths_reverse_right (l₁ l₂ : List V) :
    MutuallyInducedPaths G l₁ l₂.reverse ↔ MutuallyInducedPaths G l₁ l₂ := by
  constructor <;> intro h <;> simp_all +decide [ MutuallyInducedPaths ]

omit [Fintype W] [DecidableEq W] in
lemma sym2_ne_of_disjoint {w₁ w₂ w₃ w₄ : W}
    (_h12 : w₁ ≠ w₂) (_h34 : w₃ ≠ w₄)
    (h13 : w₁ ≠ w₃) (h14 : w₁ ≠ w₄) (_h23 : w₂ ≠ w₃) (_h24 : w₂ ≠ w₄) :
    (s(w₁, w₂) : Sym2 W) ≠ s(w₃, w₄) := by
  grind

omit [Fintype W] [DecidableEq W] in
lemma quot_out_cases (w₁ w₂ : W) :
    (s(w₁, w₂) : Sym2 W).out = (w₁, w₂) ∨ (s(w₁, w₂) : Sym2 W).out = (w₂, w₁) := by
  have := Quot.out_eq ( s(w₁, w₂) );
  grind +suggestions

omit [Fintype W] [DecidableEq W] in
lemma quot_out_pairwise_ne {w₁ w₂ w₃ w₄ : W}
    (h13 : w₁ ≠ w₃) (h14 : w₁ ≠ w₄) (h23 : w₂ ≠ w₃) (h24 : w₂ ≠ w₄) :
    (s(w₁, w₂) : Sym2 W).out.1 ≠ (s(w₃, w₄) : Sym2 W).out.1 ∧
    (s(w₁, w₂) : Sym2 W).out.1 ≠ (s(w₃, w₄) : Sym2 W).out.2 ∧
    (s(w₁, w₂) : Sym2 W).out.2 ≠ (s(w₃, w₄) : Sym2 W).out.1 ∧
    (s(w₁, w₂) : Sym2 W).out.2 ≠ (s(w₃, w₄) : Sym2 W).out.2 := by
  grind +suggestions

theorem flow_to_iae
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hV : 2 ≤ Fintype.card V) :
    Nonempty (InducedAlmostEmbedding G H) := by
  by_cases hEH : H.edgeFinset.card = 0
  · exact iae_of_no_edges (Finset.card_eq_zero.mp hEH)
  · push_neg at hEH
    obtain ⟨φ, pathChoice, hSupp, hEndpoints, hMutInd⟩ :=
      lll_good_assignment_exists hH cf hcong (Nat.pos_of_ne_zero hEH) hV
    refine ⟨{
      vertexMap := φ
      edgeMap := fun w₁ w₂ hadj =>
        let e : H.edgeFinset := ⟨s(w₁, w₂), by rwa [mem_edgeFinset]⟩
        if e.val.out.1 = w₁ then pathChoice e
        else (pathChoice e).reverse
      edgeMap_valid := fun w₁ w₂ hadj => by
        refine' ⟨ _, _, _, _, _ ⟩;
        · have := cf.valid _ ( hSupp ⟨ s(w₁, w₂), by simpa using hadj ⟩ );
          by_cases h : ( Quot.out ( s(w₁, w₂) : Sym2 W ) ).1 = w₁ <;> simp +decide [ h, List.isChain_reverse ];
          · exact this.1;
          · exact this.1.imp fun x y hxy => hxy.symm;
        · have := cf.valid ( pathChoice ⟨ s(w₁, w₂), by aesop ⟩ ) ( hSupp _ );
          grind;
        · have := cf.valid ( pathChoice ⟨ s(w₁, w₂), by aesop ⟩ ) ( hSupp _ );
          grind;
        · grind +suggestions;
        · grind +suggestions
      mutually_induced := fun w₁ w₂ w₃ w₄ h₁ h₂ hne₁ hne₂ hne₃ hne₄ => by
        set e₁ : H.edgeFinset := ⟨s(w₁, w₂), by rwa [mem_edgeFinset]⟩
        set e₂ : H.edgeFinset := ⟨s(w₃, w₄), by rwa [mem_edgeFinset]⟩
        have hne : e₁ ≠ e₂ := by
          intro h; apply_fun (fun x => x.val) at h
          exact absurd h (sym2_ne_of_disjoint h₁.ne h₂.ne hne₁ hne₂ hne₃ hne₄)
        have hpw := quot_out_pairwise_ne hne₁ hne₂ hne₃ hne₄
        have hbase := hMutInd e₁ e₂ hne hpw.1 hpw.2.1 hpw.2.2.1 hpw.2.2.2
        show MutuallyInducedPaths G
          (if e₁.val.out.1 = w₁ then pathChoice e₁ else (pathChoice e₁).reverse)
          (if e₂.val.out.1 = w₃ then pathChoice e₂ else (pathChoice e₂).reverse)
        split_ifs with h1 h2
        · exact hbase
        · rwa [mutuallyInducedPaths_reverse_right]
        · rwa [mutuallyInducedPaths_reverse_left]
        · rw [mutuallyInducedPaths_reverse_left, mutuallyInducedPaths_reverse_right]; exact hbase
    }⟩

end SimpleGraph.LLLApp
end
