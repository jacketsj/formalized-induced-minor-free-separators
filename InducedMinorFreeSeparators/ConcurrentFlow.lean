/-
# Concurrent Flow and Congestion Lower Bound

This file re-exports the concurrent flow definitions from `ConcurrentFlowDefs.lean`
and proves the congestion lower bound using the proof in `ConcurrentFlowProof/`.

## Main Results

* `congestion_lower_bound_of_no_induced_minor` - If G excludes H as an
  induced minor, then every concurrent flow on G has congestion at least
  |V|² / (45 · √(|W| + |E(H)|) · √|E(G)|).
-/
import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowDefs
import InducedMinorFreeSeparators.InducedMinor
import InducedMinorFreeSeparators.ConcurrentFlowProof.FlowInducedMinor

open Finset BigOperators
open scoped NNReal

/-! ### Congestion lower bound for induced-minor-free graphs -/

theorem congestion_lower_bound_of_no_induced_minor
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (cf : ConcurrentFlow G)
    (hfree : ¬HasInducedMinor G H)
    (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 /
      (45 * √ ((Fintype.card W : ℝ) + ↑(H.edgeFinset.card)) *
       √ ↑(G.edgeFinset.card)) < cf.congestion :=
  SimpleGraph.congestion_lower_bound_of_no_induced_minor G H cf hfree hV
