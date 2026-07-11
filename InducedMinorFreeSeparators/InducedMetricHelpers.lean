/-
# Induced Metric Helpers

Helpers for handling the disconnected G[S] case in the pure pairs dichotomy.
When G[S] is disconnected, we directly construct a well-separated pair
from the component structure rather than applying pure_pairs_fat_model.
-/
import Mathlib
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties
import InducedMinorFreeSeparators.ZHandling

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Cross-component distance bound -/

/-- When G[S] is disconnected, vertices in different components have
    G-light distance > δ₀, where S = {v : w(v) ≤ δ₀}. This is because
    any G-walk with endpoints in S and weight ≤ δ₀ must stay entirely in S
    (by walk_support_weight_le). -/
theorem cross_component_dist_gt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (S : Set V) (hS : ∀ v ∈ S, w v ≤ δ) (hS' : ∀ v, w v ≤ δ → v ∈ S)
    (x y : S)
    (hxy_diff_comp : ¬(G.comap (Subtype.val : S → V)).Reachable x y) :
    δ < @dist V (vwspPMSLight G w hw hconn).toDist x.val y.val := by
  by_contra h
  push_neg at h
  obtain ⟨p, hp⟩ := weightedDistLight_achieved hw hconn x.val y.val
  have h_dist_eq : @dist V (vwspPMSLight G w hw hconn).toDist x.val y.val = G.weightedDistLight w x.val y.val := rfl
  have hp_le : p.edgeWeightSumLight w ≤ δ := by linarith [h_dist_eq]
  have hall_in_S : ∀ v ∈ p.support, v ∈ S := fun v hv =>
    hS' v (walk_support_weight_le hw p hp_le (hS x.val x.2) (hS y.val y.2) hv)
  obtain ⟨p', _⟩ := walk_lift_to_subgraph x.2 y.2 p hall_in_S
  exact hxy_diff_comp ⟨p'⟩

omit [DecidableEq V] in
lemma induced_metric_adj_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (δ : ℝ)
    (S : Set V) (hS : ∀ v ∈ S, w v ≤ δ)
    (x y : S) (hadj : (G.comap (Subtype.val : S → V)).Adj x y) :
    @dist S (PseudoMetricSpace.induced Subtype.val (vwspPMSLight G w hw hconn)).toDist x y ≤ δ := by
  change G.weightedDistLight w x.val y.val ≤ δ
  have hle : G.weightedDistLight w x.val y.val ≤ (w x.val + w y.val) / 2 :=
    weightedDistLight_le_edge hw hadj
  linarith [hS x.val x.2, hS y.val y.2]

end
