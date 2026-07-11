import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProductIndep
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLSetup
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProbCore

/-!
# Core LLL Application — From Concurrent Flow to Induced Almost-Embedding

This file proves Lemma 4.3 of Korhonen–Lokshtanov [KL24]: given a subcubic
graph H and a concurrent flow of low congestion in G, one can find φ and
pathChoice witnessing an induced almost-embedding.

## Proof structure (following [KL24])

The proof uses the Lovász Local Lemma applied to the following random experiment:
- φ(v) is sampled uniformly at random from V(G) for each v ∈ V(H)
- For each edge uv ∈ E(H), a path is sampled from the concurrent flow
  distribution between φ(u) and φ(v)

The 5 key steps are:

1. **Vertex containment probability** (Step 1):
   Pr[w ∈ V(emap(e))] ≤ congestion / |V(G)|²

2. **Independence** (Step 2):
   For non-incident edges e₁, e₂ (with 4 distinct endpoints),
   the events {w ∈ emap(e₁)} and {z ∈ emap(e₂)} are independent.

3. **Collision probability** (Step 3):
   Pr[e₁ and e₂ collide] ≤ (|V|+2|E(G)|)/(225·|E(H)|·|E(G)|) ≤ 1/(56·|E(H)|)

4. **Dependency degree** (Step 4):
   Each collision event depends on at most 12·|E(H)| other collision events.

5. **LLL condition** (Step 5):
   4 · (1/(56·|E(H)|)) · 12·|E(H)| = 48/56 < 1, so the LLL applies.
-/

open Finset SimpleGraph Real MeasureTheory Classical
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace SimpleGraph.LLLCore

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-! ### Path existence -/

omit [Nonempty V] [DecidableRel G.Adj] in
omit [DecidableRel G.Adj] in
omit [DecidableRel G.Adj] in
/-- For distinct vertices, there exists a path with positive flow. -/
lemma exists_matching_path (cf : ConcurrentFlow G) (s t : V) (hst : s ≠ t) :
    ∃ l ∈ cf.support, l.head? = some s ∧ l.getLast? = some t ∧ 0 < cf.flow l := by
  by_contra h
  convert cf.total_flow s t hst using 1
  rw [Finset.sum_eq_zero] <;> aesop

/-! ### Vacuous case: n = 4 -/

omit [DecidableEq W] in
private lemma n_eq_4_vacuous
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 0 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (h4 : Fintype.card V = 4) : False := by
  contrapose! hcong
  refine lt_of_lt_of_le ?_ (show cf.congestion ≥ 1.5 by
    have := SimpleGraph.LLLApp.congestion_lb cf hV; norm_num [h4] at this; linarith)
  by_cases hG : G.edgeFinset.card = 0
  · norm_num [hG]
  · rw [div_lt_iff₀] <;> norm_num [h4]
    · nlinarith only [
        show 1 ≤ Real.sqrt (H.edgeFinset.card : ℝ) by
          exact Real.le_sqrt_of_sq_le (mod_cast hEH),
        show 1 ≤ Real.sqrt (G.edgeFinset.card : ℝ) by
          exact Real.le_sqrt_of_sq_le (mod_cast Nat.one_le_iff_ne_zero.mpr hG),
        Real.mul_self_sqrt (Nat.cast_nonneg H.edgeFinset.card),
        Real.mul_self_sqrt (Nat.cast_nonneg G.edgeFinset.card)]
    · positivity

/-! ### Trivial case: |E(H)| = 1 -/

omit [DecidableRel G.Adj] in
private lemma single_edge_case
    (_hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hEH_eq : H.edgeFinset.card = 1)
    (hV : 2 ≤ Fintype.card V)
    (_hVbig : 3 < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hEH_eq
  simp_all +decide [Finset.ext_iff]
  obtain ⟨l, hl⟩ : ∃ l ∈ cf.support, l.head? = some (Classical.arbitrary V) ∧
      l.getLast? = some (Classical.choose (Finset.exists_mem_ne hV (Classical.arbitrary V))) :=
    Exists.imp (by tauto)
      (exists_matching_path cf _ _
        (Classical.choose_spec (Finset.exists_mem_ne hV (Classical.arbitrary V)) |>.2.symm))
  refine ⟨fun x => if x = (Quot.out e).1 then Classical.arbitrary V
      else Classical.choose (Finset.exists_mem_ne hV (Classical.arbitrary V)),
    fun _ => l, ?_, ?_⟩ <;> simp +decide [hl]
  specialize he (Quot.mk _ ((Quot.out e).1, (Quot.out e).1))
  simp_all +decide
  grind +suggestions

/-! ### Step 1: Vertex containment probability

Pr[w ∈ V(emap(e))] = (1/|V|²) · Σ_{(a,b)} Σ_{P: a-b path, w∈P} cf.flow(P)
                    = cf.vertexFlow(w) / |V|²
                    ≤ cf.congestion / |V|²
-/

omit [DecidableRel G.Adj] in
/-- The vertex flow (total flow through a vertex) is at most the congestion. -/
lemma vertexFlow_le_congestion (cf : ConcurrentFlow G) (w : V) :
    cf.vertexFlow w ≤ cf.congestion := by
  exact Finset.le_sup' (fun v => cf.vertexFlow v) (Finset.mem_univ w)

/-! ### Step 3: Collision probability bound

For non-incident edges e₁, e₂, by union bound over (w,z) pairs:
  Pr[collision] ≤ (|V| + 2|E(G)|) · (congestion/|V|²)²
With congestion ≤ |V|²/(15·√|E(H)|·√|E(G)|):
  ≤ (|V| + 2|E(G)|) / (225·|E(H)|·|E(G)|)
  ≤ 1/(56·|E(H)|)  [using |V| ≤ 2|E(G)| for connected G]
-/

/-
Arithmetic helper: the collision probability bound.
-/
lemma collision_prob_arithmetic
    (n eH eG : ℕ) (hn : 4 < n) (heH : 1 < eH) (heG : 0 < eG)
    (hconn : n ≤ eG + 1) :
    ((n : ℝ) + 2 * eG) / (225 * eH * eG) ≤ 1 / (56 * eH) := by
  rw [ div_le_div_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 4 : ℝ ) < n ), ( by norm_cast : ( n : ℝ ) ≤ eG + 1 ), ( by norm_cast : ( 1 : ℝ ) < eH ), ( by norm_cast : ( 0 : ℝ ) < eG ), mul_pos ( by positivity : ( 0 : ℝ ) < eH ) ( by positivity : ( 0 : ℝ )
 < eG ) ]

/-! ### Step 5: LLL condition

4 · p · d ≤ 1 where p ≤ 1/(56·|E(H)|) and d ≤ 12·|E(H)|.
-/

/-- The LLL condition 4pd ≤ 1. -/
lemma lll_condition :
    4 * (1 / (56 : ℝ)) * 12 ≤ 1 := by norm_num

/-! ### Concurrent flow implies connectivity -/

/-
A concurrent flow on G with |V| ≥ 2 implies G has enough edges: |V| ≤ |E(G)| + 1.
    This follows because the concurrent flow requires paths between all pairs,
    which means G is connected, and a connected graph on n vertices has ≥ n-1 edges.
-/
lemma cf_implies_enough_edges (cf : ConcurrentFlow G) (_hV : 2 ≤ Fintype.card V) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  -- From the concurrent flow definition, for any distinct s,t : V, cf.total_flow gives ∑ flow = 1 on paths from s to t. So there is at least one path from s to t in cf.support.
  have h_connected : ∀ s t : V, s ≠ t → G.Reachable s t := by
    intro s t hst
    obtain ⟨l, hl⟩ : ∃ l ∈ cf.support, l.head? = some s ∧ l.getLast? = some t := by
      obtain ⟨l, hl⟩ := exists_matching_path cf s t hst;
      grind +splitIndPred;
    have h_path : ∀ {l : List V}, l.IsChain G.Adj → ∀ s t : V, l.head? = some s → l.getLast? = some t → G.Reachable s t := by
      intros l hl s t hs ht; induction' l with a l ih generalizing s t <;> simp_all +decide ;
      cases l <;> simp_all +decide;
      exact hl.1.reachable.trans ( ih _ _ rfl ht );
    exact h_path ( cf.valid l hl.1 |>.1 ) s t hl.2.1 hl.2.2;
  -- Since G is connected, we can apply the fact that a connected graph on n vertices has at least n-1 edges.
  have h_connected_graph : G.Connected := by
    exact SimpleGraph.Connected.mk fun s t => if h : s = t then h.symm ▸ SimpleGraph.Reachable.refl _ else h_connected s t h;
  obtain ⟨T, hT⟩ : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
    have := h_connected_graph.exists_isTree_le;
    exact this;
  have := hT.2.card_edgeFinset;
  exact this ▸ Nat.succ_le_succ ( Finset.card_mono ( by aesop ) )

/-! ### Vacuous case: 5 ≤ n ≤ 11 with |E(H)| ≥ 2

When 5 ≤ |V| ≤ 11 and |E(H)| ≥ 2 and G has a concurrent flow
(so |E(G)| ≥ |V| - 1 by connectivity), the congestion lower bound
2(n-1)/n combined with hcong ≤ n²/(15√(|E(H)|)√(|E(G)|)) leads to a
contradiction because 30√2(n-1)^{3/2} > n³ for n ≤ 11. -/

omit [DecidableEq W] in
private lemma medium_n_vacuous
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn_ge : 4 < Fintype.card V)
    (hn_le : Fintype.card V ≤ 11) : False := by
  -- Bycf_implies_enough_edges, we have n ≤ |E(G)| + 1, so |E(G)| ≥ n-1.
  have h_edges_G : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    exact cf_implies_enough_edges cf hV;
  -- Bycf_implies_enough_edges, we have n ≤ |E(G)| + 1, so |E(G)| ≥ n-1. Also, from congestion_lb, we have cf.congestion ≥ 2(n-1)/n.
  have h_congestion_ge : cf.congestion ≥ 2 * (Fintype.card V - 1) / (Fintype.card V) := by
    exact div_le_iff₀ ( by positivity ) |>.2 ( by linarith [ SimpleGraph.LLLApp.congestion_lb cf hV ] );
  -- Combining the inequalities from hcong and h_congestion_ge, we get:
  have h_combined : 2 * (Fintype.card V - 1) / (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / (15 * Real.sqrt (H.edgeFinset.card : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ)) := by
    exact h_congestion_ge.trans hcong;
  -- Squaring both sides of the inequality, we get:
  have h_squared : (2 * (Fintype.card V - 1) / (Fintype.card V : ℝ)) ^ 2 ≤ (Fintype.card V : ℝ) ^ 4 / (225 * (H.edgeFinset.card : ℝ) * (G.edgeFinset.card : ℝ)) := by
    convert pow_le_pow_left₀ ( div_nonneg ( mul_nonneg zero_le_two ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_nonneg _ ) ) h_combined 2 using 1 ; ring_nf ; norm_num;
  rw [ div_pow, div_le_div_iff₀ ] at h_squared <;> norm_cast at * <;> try positivity;
  · interval_cases Fintype.card V <;> norm_num [ Int.subNatNat_eq_coe ] at * <;> nlinarith;
  · exact mul_pos ( mul_pos ( by decide ) ( by linarith ) ) ( by linarith )

/-! ### Main theorem -/

theorem exists_good_assignment
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 0 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hVbig : 3 < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  -- Case 1: |V| = 4 → hypothesis is contradictory
  by_cases h4 : Fintype.card V = 4
  · exact (n_eq_4_vacuous cf hcong hEH hV h4).elim
  -- Case 2: |E(H)| = 1 → trivial (no non-incident edge pairs)
  by_cases hE1 : H.edgeFinset.card = 1
  · exact single_edge_case hH cf hE1 hV hVbig
  -- Now we know |V| ≥ 5 and |E(H)| ≥ 2
  have hn5 : 4 < Fintype.card V := lt_of_le_of_ne hVbig (Ne.symm h4)
  have hEH2 : 1 < H.edgeFinset.card := lt_of_le_of_ne hEH (Ne.symm hE1)
  -- Case 3: 5 ≤ |V| ≤ 11 and |E(H)| ≥ 2 → vacuous
  by_cases hn11 : Fintype.card V ≤ 11
  · exact (medium_n_vacuous cf hcong hEH2 hV hn5 hn11).elim
  -- Case 4: |V| ≥ 12 and |E(H)| ≥ 2 → LLL argument
  push_neg at hn11
  -- Apply the Lovász Local Lemma to the product probability space where
  -- φ maps vertices uniformly at random and paths are sampled from the
  -- concurrent flow distribution between φ-images of edge endpoints.
  -- The 5 steps from [KL24] give:
  -- Step 1: Pr[w ∈ emap(e)] ≤ congestion/n² (by vertexFlow_le_congestion)
  -- Step 2: Non-incident edges are independent (disjoint variable sets)
  -- Step 3: Pr[collision] ≤ 1/(56|E(H)|) (by collision_prob_arithmetic)
  -- Step 4: Dependency degree ≤ 12|E(H)| (subcubic ⇒ ≤12 incident edges)
  -- Step 5: 4·p·d = 48/56 < 1 (by lll_condition)
  exact SimpleGraph.ProbCore.exists_good_from_lll hH cf hcong hEH2 hV hn11

end SimpleGraph.LLLCore
end
