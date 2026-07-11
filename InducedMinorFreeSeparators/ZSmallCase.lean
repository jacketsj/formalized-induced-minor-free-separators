/-
# Z-Small Case: Connected G[S]

When G[S] is connected, apply pure_pairs_fat_model to G[S] and convert outputs.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties
import InducedMinorFreeSeparators.ZHandling

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
Walks in G.comap Subtype.val lift to walks in G with the same light weight.
-/
omit [Fintype V] [DecidableEq V] in
omit [DecidableEq V] in
lemma walk_comap_to_walk {G : SimpleGraph V} {S : Set V}
    {x y : S} (p : (G.comap (Subtype.val : S → V)).Walk x y)
    (w : V → ℝ) :
    ∃ (q : G.Walk x.val y.val),
      q.edgeWeightSumLight w = p.edgeWeightSumLight (w ∘ Subtype.val) := by
  refine' ⟨ p.map ( SimpleGraph.Hom.comap _ _ ), _ ⟩;
  induction p <;> simp_all +decide [ SimpleGraph.Walk.map ];
  · rfl;
  · simp_all +decide [ SimpleGraph.Walk.edgeWeightSumLight ]

/-
dist_G_light ≤ dist_{G[S]_light} for x, y ∈ S.
-/
omit [Fintype V] [DecidableEq V] in
lemma vwsp_dist_subgraph_ge {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (_hconn : G.Connected)
    {S : Set V} (hconn' : (G.comap (Subtype.val : S → V)).Connected)
    (x y : S) :
    G.weightedDistLight w x.val y.val ≤
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y := by
  refine' le_csInf _ _ <;> norm_num;
  · exact ⟨ _, ⟨ hconn'.exists_isPath x y |> Classical.choose, rfl ⟩ ⟩;
  · intro p
    obtain ⟨q, hq⟩ := walk_comap_to_walk p w;
    refine' le_trans ( csInf_le _ ⟨ q, rfl ⟩ ) hq.le;
    exact ⟨ 0, Set.forall_mem_range.2 fun p => edgeWeightSumLight_nonneg hw p ⟩

/-
hG_metric for G[S]: adjacent vertices have light dist ≤ δ when all weights ≤ δ.
-/
omit [Fintype V] [DecidableEq V] in
lemma comap_adj_dist_le {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {S : Set V} {δ : ℝ} (hS : ∀ v ∈ S, w v ≤ δ)
    (_hconn' : (G.comap (Subtype.val : S → V)).Connected)
    (x y : S) (hadj : (G.comap (Subtype.val : S → V)).Adj x y) :
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y ≤ δ := by
  -- Since x and y are adjacent in G[S], there's an edge between them, so the total weight is (w(x.val) + w(y.val))/2.
  have h_edge_weight : (SimpleGraph.comap Subtype.val G).weightedDistLight (w ∘ Subtype.val) x y ≤ (w x.val + w y.val) / 2 := by
    apply weightedDistLight_le_edge;
    · exact fun v => hw _;
    · exact hadj;
  linarith [ hS x x.2, hS y y.2 ]

end
