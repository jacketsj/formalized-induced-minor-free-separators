/-
# Concurrent Flow Definitions

Core definitions for concurrent flows on graphs.
This file is separate from `ConcurrentFlow.lean` to avoid import cycles
with the proof files in `ConcurrentFlowProof/`.

## Main Definitions

* `ConcurrentFlow` - A concurrent flow on a graph, routing unit flow between
  all pairs of vertices using paths (represented as lists).
* `ConcurrentFlow.vertexFlow` - The total flow through a vertex.
* `ConcurrentFlow.congestion` - The maximum vertex flow (over all vertices).
-/
import Mathlib

open Finset BigOperators
open scoped NNReal

/-! ### Concurrent flow -/

/-- A concurrent flow on a simple graph G routes unit flow between every
ordered pair of distinct vertices using a collection of paths (represented
as lists of vertices). -/
structure ConcurrentFlow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The finite set of paths (as vertex lists) used by the flow. -/
  support : Finset (List V)
  /-- Every path in the support is a valid simple path in G:
      it forms a chain under adjacency, has no repeated vertices,
      and has length at least 2 (i.e., at least one edge). -/
  valid : ∀ l ∈ support, l.IsChain G.Adj ∧ l.Nodup ∧ 2 ≤ l.length
  /-- The flow value assigned to each path. -/
  flow : List V → ℝ≥0
  /-- Flow is zero outside the support. -/
  flow_support : ∀ l, l ∉ support → flow l = 0
  /-- For every ordered pair of distinct vertices (s,t), the total flow
      on paths from s to t equals 1. -/
  total_flow : ∀ s t : V, s ≠ t →
    ∑ l ∈ support.filter (fun l => l.head? = some s ∧ l.getLast? = some t),
      (flow l : ℝ) = 1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The total flow through vertex v: the sum of flow values over all paths
that pass through v. -/
def ConcurrentFlow.vertexFlow (cf : ConcurrentFlow G) (v : V) : ℝ :=
  ∑ l ∈ cf.support.filter (fun l => v ∈ l), (cf.flow l : ℝ)

/-- The congestion of a concurrent flow: the maximum vertex flow over all
vertices. Uses `Finset.sup'` on the nonempty universe. -/
noncomputable def ConcurrentFlow.congestion [Nonempty V] (cf : ConcurrentFlow G) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun v => cf.vertexFlow v)
