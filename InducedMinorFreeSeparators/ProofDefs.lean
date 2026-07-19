/-
# Proof-Level Definitions for String Graph Separators

This file contains definitions used in the **proof** (but not the statement)
of the main separator theorem. For the definitions that appear in the
statement itself, see `Defs.lean`.

## Main Definitions

* `QbarFeasible` - Feasibility condition for the Q̄ optimization problem
* `Qbar` - The extremal line-embedded spread Q̄(G)
* `Qspread` - The unrelaxed metric spread Q(G)
* `QDual` - LP dual of Q(G) via fractional routings
* Cover-vertex expansion (`coverBoundarySize`, `coverExpansion`)
* Non-expansive embeddings (`IsNonExpansive`, `pairDistSum`, etc.)
-/
import Mathlib
import Padding.EmbeddingDefs
import InducedMinorFreeSeparators.Defs

open Finset BigOperators

variable {V : Type*}

/-! ## Extremal Line-Embedded Spread Q̄(G) -/

/-- A pair `(ω, f)` is feasible for the Q̄ optimization problem on graph `G`. -/
structure QbarFeasible [Fintype V] (G : SimpleGraph V) (ω f : V → ℝ) : Prop where
  omega_nonneg : ∀ v, 0 ≤ ω v
  omega_sum : ∑ v : V, ω v ≤ 1
  edge_constraint : ∀ u v, G.Adj u v → |f u - f v| ≤ ω u + ω v

/-- The objective value of a Q̄ feasible solution. -/
noncomputable def QbarObj [Fintype V] (f : V → ℝ) : ℝ :=
  ∑ u : V, ∑ v : V, |f u - f v|

/-- The extremal line-embedded spread Q̄(G), defined as the supremum of
`Σ_{u,v} |f(u) - f(v)|` over all feasible pairs `(ω, f)`. -/
noncomputable def Qbar [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup { val | ∃ ω f : V → ℝ, QbarFeasible G ω f ∧ val = QbarObj f }

/-- The set of Q̄ objective values is bounded above for connected graphs. -/
theorem Qbar_bddAbove [Fintype V] (G : SimpleGraph V) (hconn : G.Connected) :
    BddAbove { val | ∃ ω f : V → ℝ, QbarFeasible G ω f ∧ val = QbarObj f } := by
  have h_path : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ Fintype.card V := by
    intro u v
    obtain ⟨p, hp⟩ : ∃ p : G.Walk u v, p.IsPath := by exact SimpleGraph.Connected.exists_isPath hconn u v
    exact ⟨p, by have := hp.length_lt; linarith⟩
  have h_edge_constraint : ∀ (ω f : V → ℝ), QbarFeasible G ω f → ∀ u v : V,
      ∀ p : G.Walk u v, |f u - f v| ≤
        ∑ i ∈ Finset.range p.length, (ω (p.getVert i) + ω (p.getVert (i + 1))) := by
    intro ω f hf u v p
    have h_step : ∀ i ∈ Finset.range p.length,
        |f (p.getVert i) - f (p.getVert (i + 1))| ≤
          ω (p.getVert i) + ω (p.getVert (i + 1)) := by
      intro i hi
      have h_edge : G.Adj (p.getVert i) (p.getVert (i + 1)) := by
        convert p.adj_getVert_succ _; exact Finset.mem_range.mp hi
      exact hf.edge_constraint _ _ h_edge
    convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum h_step using 1
    rw [Finset.sum_range_sub']; aesop
  have h_bound : ∀ (ω f : V → ℝ), QbarFeasible G ω f → ∀ u v : V,
      |f u - f v| ≤ 2 * Fintype.card V := by
    intro ω f hf u v
    obtain ⟨p, hp⟩ := h_path u v
    have h_sum : ∑ i ∈ Finset.range p.length,
        (ω (p.getVert i) + ω (p.getVert (i + 1))) ≤ 2 * Fintype.card V := by
      have h_sum : ∑ i ∈ Finset.range p.length,
          (ω (p.getVert i) + ω (p.getVert (i + 1))) ≤
            ∑ i ∈ Finset.range p.length, 2 * (∑ v : V, ω v) :=
        Finset.sum_le_sum fun i _ => by
          linarith [hf.omega_nonneg (p.getVert i), hf.omega_nonneg (p.getVert (i + 1)),
            Finset.single_le_sum (fun v _ => hf.omega_nonneg v) (Finset.mem_univ (p.getVert i)),
            Finset.single_le_sum (fun v _ => hf.omega_nonneg v)
              (Finset.mem_univ (p.getVert (i + 1)))]
      simp_all +decide [← Finset.mul_sum _ _ _]
      exact h_sum.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [show (p.length : ℝ) ≤ Fintype.card V by exact_mod_cast hp,
          show (∑ v : V, ω v : ℝ) ≤ 1 by exact_mod_cast hf.omega_sum]) zero_le_two)
    exact le_trans (h_edge_constraint ω f hf u v p) h_sum
  exact ⟨(Fintype.card V) ^ 2 * (2 * Fintype.card V), by
    rintro x ⟨ω, f, hf, rfl⟩
    exact le_trans (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
      h_bound ω f hf u v) (by simp +decide [sq, mul_assoc])⟩

/-- Any feasible solution gives a lower bound on Q̄(G) for connected graphs. -/
theorem Qbar_le_of_feasible [Fintype V] (G : SimpleGraph V) (hconn : G.Connected)
    {ω f : V → ℝ} (hfeas : QbarFeasible G ω f) :
    QbarObj f ≤ Qbar G :=
  le_csSup (Qbar_bddAbove G hconn) ⟨ω, f, hfeas, rfl⟩

/-! ## Cover-Vertex Expansion -/

/-- A set `C` is a vertex cover of the edges between `S` and `Sᶜ` in graph `G`. -/
def SimpleGraph.IsEdgeCutCover [DecidableEq V] (G : SimpleGraph V)
    (S C : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S → v ∉ S → u ∈ C ∨ v ∈ C

/-- The cover-boundary size: minimum cardinality of a vertex cover of E(S, V\S). -/
noncomputable def SimpleGraph.coverBoundarySize [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sInf { c | ∃ C : Finset V, C.card = c ∧ G.IsEdgeCutCover S C }

/-- The covered vertex expansion of a set S: |∂̇S| / |S|. -/
noncomputable def SimpleGraph.coverExpansionAt [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℝ :=
  (G.coverBoundarySize S : ℝ) / S.card

/-- The covered vertex expansion of the graph G:
`ψ(G) = min_{S : |S| ≤ n/2} |∂̇S| / |S|`. -/
noncomputable def SimpleGraph.coverExpansion [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf { ψ | ∃ S : Finset V, 2 * S.card ≤ Fintype.card V ∧
    ψ = G.coverExpansionAt S }

/-! ## Non-Expansive Embeddings and Average Distortion

The shared notions `IsNonExpansive`, `pairDistSum`, `embeddingSum`, and
`avgDistortion` are imported from `Padding.EmbeddingDefs`, so the separator proof
uses the same API as the Rabinovich embedding theorem from `Padding/`.
-/

/-! ## Unrelaxed Metric Spread Q(G) -/

/-- The weighted length of a walk, where each edge uv has length w(u) + w(v). -/
noncomputable def SimpleGraph.Walk.edgeWeightSum {V : Type*} {G : SimpleGraph V}
    (w : V → ℝ) : {u v : V} → G.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v') _ p => (w u + w v') + p.edgeWeightSum w

/-- The shortest-path distance with edge weights w(u) + w(v). -/
noncomputable def SimpleGraph.weightedDist {V : Type*}
    (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ :=
  ⨅ (p : G.Walk u v), p.edgeWeightSum w

/-- The unrelaxed metric spread Q(G). -/
noncomputable def Qspread {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup { val | ∃ w : V → ℝ, (∀ v, 0 ≤ w v) ∧ (∑ v, w v ≤ 1) ∧
    val = ∑ u : V, ∑ v : V, G.weightedDist w u v }

/-! ## Vertex Load and LP Dual of Q(G) via Fractional Routings

The LP formulation of Q(G) has a constraint for each path P from u to v:
  t(u,v) ≤ Σ_x w(x) · vertexLoad(P, x)

The LP dual assigns a variable λ(u,v,P) ≥ 0 to each path constraint.
The dual problem is:

  QDual(G) = min over fractional routings R of max_x congestion_R(x)

where a fractional routing satisfies Σ_P R(u,v,P) = 1 for each pair (u,v)
and congestion_R(x) = Σ_{u,v,P} R(u,v,P) · vertexLoad(P, x).

LP strong duality Q(G) = QDual(G) is proved using Farkas' lemma
(the hyperplane separation theorem for proper cones).
-/

/-- The number of edges in a walk that are incident to vertex `x`.
For a walk `u → v' → ... → v`, the edge `(u, v')` contributes 1 to the load
of each of `u` and `v'`. -/
def SimpleGraph.Walk.vertexLoad [DecidableEq V] {G : SimpleGraph V}
    (x : V) : {u v : V} → G.Walk u v → ℕ
  | _, _, .nil => 0
  | u, _, .cons (v := v') _ p =>
    (if x = u then 1 else 0) + (if x = v' then 1 else 0) + p.vertexLoad x

/-- Edge weight sum equals the sum of weights times vertex loads:
`edgeWeightSum(P, w) = Σ_x w(x) · vertexLoad(P, x)`. -/
lemma edgeWeightSum_eq_sum_vertexLoad [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : V → ℝ) {u v : V} (P : G.Walk u v) :
    P.edgeWeightSum w = ∑ x : V, w x * ↑(P.vertexLoad x) := by
  induction P with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum, SimpleGraph.Walk.vertexLoad]
  | cons hadj p ih =>
    simp only [SimpleGraph.Walk.edgeWeightSum, SimpleGraph.Walk.vertexLoad, Nat.cast_add,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [ih]
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The congestion at vertex `x` under a fractional routing `R`. -/
noncomputable def routingCongestion [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (R : (u v : V) → G.Path u v → ℝ) (x : V) : ℝ :=
  ∑ u, ∑ v, ∑ P : G.Path u v, R u v P * ↑((P : G.Walk u v).vertexLoad x)

/-- The LP dual of Q(G): infimum over fractional routings of the max congestion.

A fractional routing assigns nonneg weights R(u,v,P) ≥ 0 to each path P
from u to v, with Σ_P R(u,v,P) = 1 for each pair (u,v). The congestion at
vertex x is Σ_{u,v,P} R(u,v,P) · vertexLoad(P, x).

For connected graphs, LP strong duality gives QDual(G) = Qspread(G),
proved using Farkas' lemma (hyperplane separation for proper cones). -/
noncomputable def QDual [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf { μ : ℝ | ∃ R : (u v : V) → G.Path u v → ℝ,
    (∀ u v P, 0 ≤ R u v P) ∧
    (∀ u v, ∑ P : G.Path u v, R u v P = 1) ∧
    μ = Finset.univ.sup' Finset.univ_nonempty (fun x => routingCongestion R x) }

/-! ### Positive homogeneity of edge weight sums and shortest-path distances -/

/-- Edge weight sum scales linearly: (t * w) gives t * edgeWeightSum. -/
lemma edgeWeightSum_smul {G : SimpleGraph V}
    (t : ℝ) (w : V → ℝ) {u v : V} (P : G.Walk u v) :
    P.edgeWeightSum (fun x => t * w x) = t * P.edgeWeightSum w := by
  induction P with
  | nil => simp [SimpleGraph.Walk.edgeWeightSum]
  | cons hadj p ih => simp [SimpleGraph.Walk.edgeWeightSum, ih]; ring

/-- Shortest-path distance is positively homogeneous:
`d_{t·w}(u,v) = t · d_w(u,v)` for `t ≥ 0`. -/
lemma weightedDist_smul {G : SimpleGraph V}
    (t : ℝ) (ht : 0 ≤ t) (w : V → ℝ) (u v : V) :
    G.weightedDist (fun x => t * w x) u v = t * G.weightedDist w u v := by
  simp only [SimpleGraph.weightedDist, edgeWeightSum_smul]
  exact (Real.mul_iInf_of_nonneg ht _).symm

/-- The Qspread set is nonempty (w = 0 is feasible). -/
lemma Qspread_set_nonempty [Fintype V] (G : SimpleGraph V) :
    { val | ∃ w : V → ℝ, (∀ v, 0 ≤ w v) ∧ (∑ v, w v ≤ 1) ∧
      val = ∑ u : V, ∑ v : V, G.weightedDist w u v }.Nonempty :=
  ⟨_, fun _ => 0, fun _ => le_refl _, by simp, rfl⟩
