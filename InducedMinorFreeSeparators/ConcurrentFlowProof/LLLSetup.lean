import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL

/-!
# LLL Application: Direct proof of good assignment existence

The proof applies the Lovász Local Lemma to the concurrent flow setting.
We use the combinatorial LLL with the weighted PMF on assignments.
-/

open Finset SimpleGraph Real MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace SimpleGraph.LLLApp

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-
The congestion of any concurrent flow is at least 2(|V|-1)/|V|.
-/
omit [DecidableRel G.Adj] in
lemma congestion_lb (cf : ConcurrentFlow G) (hV : 2 ≤ Fintype.card V) :
    (2 : ℝ) * ((Fintype.card V : ℝ) - 1) ≤ cf.congestion * Fintype.card V := by
  -- By definition of congestion, we have that the total vertex flow is at least 2 * (Fintype.card V - 1).
  have h_total_vertex_flow : ∑ v : V, cf.vertexFlow v ≥ 2 * (Fintype.card V - 1) := by
    -- By definition of $cf $, we know that $\sum_{l \ in \text{support}} \text{flow}(l) = |V|(|V|-1)$.
    have h_total_flow : ∑ l ∈ cf.support, (cf.flow l : ℝ) = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      convert cf.total_flow;
      constructor;
      · exact fun h s t hst => cf.total_flow s t hst;
      · intro h
        have h_total : ∑ l ∈ cf.support, (cf.flow l : ℝ) = ∑ s : V, ∑ t : V, if s ≠ t then ∑ l ∈ cf.support.filter (fun l => l.head? = some s ∧ l.getLast? = some t), (cf.flow l : ℝ) else 0 := by
          rw [ Finset.sum_comm ];
          simp +decide [ Finset.sum_ite ];
          rw [ Finset.sum_sigma' ];
          rw [ ← Finset.sum_biUnion ];
          · refine' Finset.sum_subset _ _ <;> intro l hl <;> simp_all +decide [ Finset.mem_biUnion ];
            · rcases l with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
              · exact absurd ( cf.valid _ hl ) ( by simp +decide );
              · exact absurd ( cf.valid _ hl ) ( by simp +decide );
              · have := cf.valid _ hl;
                induction l using List.reverseRecOn <;> aesop;
            · exact fun h => cf.flow_support l h;
          · intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
            grind;
        simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
        rw [ Nat.cast_pred ( by linarith ) ];
    -- By definition of $vertexFlow $, we know that $\sum_{v} vertexFlow (v) = \sum_{l \in support} flow(l) \cdot |l|$.
    have h_vertex_flow_sum : ∑ v : V, cf.vertexFlow v = ∑ l ∈ cf.support, (cf.flow l : ℝ) * l.length := by
      simp +decide only [ConcurrentFlow.vertexFlow, sum_filter];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +contextual [ Finset.sum_ite ];
      intro l hl; rw [ mul_comm ] ; congr;
      convert List.toFinset_card_of_nodup ( cf.valid l hl |>.2.1 );
      aesop;
    rw [ h_vertex_flow_sum ];
    refine' le_trans _ ( Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr ( cf.valid l hl |>.2.2 ) ) ( NNReal.coe_nonneg _ ) ) ; simp +decide;
    rw [ ← Finset.sum_mul _ _ _, h_total_flow ] ; nlinarith [ show ( Fintype.card V : ℝ ) ≥ 2 by norm_cast ];
  refine' le_trans h_total_vertex_flow _;
  exact le_trans ( Finset.sum_le_sum fun _ _ => show cf.vertexFlow _ ≤ cf.congestion from Finset.le_sup' ( fun v => cf.vertexFlow v ) <| Finset.mem_univ _ ) <| by simp +decide [ mul_comm ] ;

/-
For |V| ≤ 3 and positive edges, the congestion bound hypothesis is vacuously false.
-/
omit [DecidableEq W] in
lemma small_V_vacuous
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 0 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hVsmall : Fintype.card V ≤ 3) : False := by
  interval_cases _ : Fintype.card V <;> simp_all +decide;
  · have := congestion_lb cf ( by linarith );
    rcases n : #G.edgeFinset with ( _ | _ | n ) <;> simp_all +decide;
    · linarith;
    · contrapose! hcong;
      rw [ div_lt_iff₀ ] <;> nlinarith [ show 1 ≤ Real.sqrt ( H.edgeFinset.card : ℝ ) from Real.le_sqrt_of_sq_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ) ];
    · refine' absurd hcong ( not_le_of_gt _ );
      refine' lt_of_lt_of_le _ ( show cf.congestion ≥ 1 by linarith );
      rw [ div_lt_iff₀ ] <;> norm_num;
      · exact lt_of_lt_of_le ( by norm_num ) ( mul_le_mul ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| Nat.cast_le.mpr <| Finset.card_pos.mpr <| by contrapose! hEH; aesop ) <| by positivity ) ( Real.sqrt_le_sqrt <| show ( ↑_ + 1 + 1 : ℝ ) ≥ 1 by linarith ) ( by positivity ) <| by positivity );
      · exact mul_pos ( mul_pos ( by norm_num ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( by contrapose! hEH; aesop ) ) ) ) ) ( Real.sqrt_pos.mpr ( by positivity ) );
  · have h_cong : cf.congestion ≥ 2 * ((3 : ℝ) - 1) / 3 := by
      have := congestion_lb cf ( by linarith ) ; norm_num [ ‹Fintype.card V = 3› ] at this ⊢; linarith;
    have h_cong : 3 ^ 2 / (15 * Real.sqrt (H.edgeFinset.card : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ)) ≤ 3 ^ 2 / (15 * 1 * 1) := by
      gcongr <;> norm_num;
      · exact hEH;
      · rintro rfl; norm_num at *;
        have := cf.total_flow; simp_all +decide [ SimpleGraph.edgeFinset ] ;
        linarith;
    grind

end SimpleGraph.LLLApp
end
