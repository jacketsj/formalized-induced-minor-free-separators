/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.AsymptoticDimension
import Padding.Defs.MuModel
import Padding.RegionIntersection.AsymptoticDimensionHelpers
import Padding.RegionIntersection.IntersectionModel
import Padding.RegionIntersection.RegionStepInductive

/-! # Asymptotic Dimension of Region Intersection Graphs

## Radius bookkeeping (correction to the source transcription)

The reference proof transcribed in `AsymptoticDimensionProof.tex` states the
`(δ, ρ)`-partition radius as `ρ = 2γ + 1 + (t-2)·δ`, measured as a **radius** (every
δ-component is within `ρ` of some centre).  The Lean definition `DeltaRhoPartition`
records the stronger **diameter** bound `G.dist u v ≤ ρ` for every pair `u, v` in a common
δ-component.  Two effects change the constant relative to the source:

* **Radius → diameter.** The central ball `V_{0,2γ+1}` has radius `2γ+1` about the BFS root
  `x*`, hence *diameter* at most `4γ+2` (triangle inequality through `x*`).

* **Forced model radius `γ+δ`.** The inductive step applies the lemma at `t-1` with model
  radius `γ + δ` (the surviving auxiliary-graph component sits at distance up to `γ+δ` from
  the band centre), so `γ` grows by `δ` per level.

The self-consistent diameter radius is therefore

  `ρ(t, γ) = 4γ + 4·(t-2)·δ + 2`,

which closes the recursion exactly: `ρ(t-1, γ+δ) = 4(γ+δ) + 4((t-1)-2)δ + 2 = ρ(t, γ)`,
dominates the central diameter `4γ+2` for `t ≥ 3`, and dominates the base-case diameter
`2γ+1` at `t = 2`.  At the top level (`γ = δ`) it gives partition diameter `4·(t-1)·δ + 2`,
the same `O(t·δ)` bound (up to the leading constant) needed by the downstream sparse-cover /
padded-decomposition chain.
-/

open SimpleGraph Set

universe u

/-- **Lemma (Region Step)**: Let `G` be a connected graph, `H` a graph, `μ` a region
intersection model of `G` over `H`, `S ⊆ V(G)`, `t ≥ 2`, and `γ ≥ δ ≥ 1`.
If there is no `(μ, S, γ, t)`-model, then `S` has a `(δ, 4γ+4(t-2)δ+2)`-partition
in `G` of size at most `2^{t-2}`.

(The radius `4γ+4(t-2)δ+2` is the self-consistent value for the diameter-based
`DeltaRhoPartition`; see the module docstring.) -/
theorem region_step {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (S : Set V₁) (t : ℕ) (γ δ : ℕ)
    (ht : 2 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ t)) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2) S (2 ^ (t - 2))) := by
  -- Proof by strong induction on `t`, generalised over the graph, host and model (only `δ`
  -- stays fixed).  This generality is essential: the inductive step recurses on an
  -- auxiliary graph over a *different* host.
  suffices key : ∀ t : ℕ, 2 ≤ t → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
      {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
      δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' t) →
      Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (t - 2) * δ + 2) S' (2 ^ (t - 2))) from
    key t ht μ S γ hγδ hconn hno_model
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  intro ht W₁ W₂ G' H' μ' S' γ' hγδ' hconn' hno_model'
  -- Base case: t = 2
  by_cases ht2 : t = 2
  · subst ht2
    simp only [Nat.reduceSub, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.reducePow]
    -- region_step_base gives diameter `2γ+1`; relax to `4γ+2`.
    obtain ⟨P⟩ := region_step_base μ' S' γ' δ hγδ' hδ hconn' hno_model'
    exact ⟨P.mono_rho (by omega)⟩
  · -- Inductive step: t ≥ 3.  Delegated to `region_step_inductive`, which carries out the
    -- BFS-band / auxiliary-intersection-graph construction of the reference proof.
    have ht3 : 3 ≤ t := by omega
    exact region_step_inductive μ' ih S' γ' ht3 hγδ' hδ hconn' hno_model'

/-- **Theorem (Asymptotic Dimension of Region Intersection Graphs)**

For every `δ ≥ 1`, a connected region intersection graph over a `Kₜ`-minor-free graph has
a `(δ, 4(t-1)δ+2)`-partition of `V(G)` of size at most `2^{t-2}`.

(The radius `4(t-1)δ+2` is the honest top-level value `4γ+4(t-2)δ+2` at `γ = δ`; see the
module docstring for the radius/diameter bookkeeping.) -/
theorem region_intersection_asymptotic_dimension
    {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (δ : ℕ) (hδ : 1 ≤ δ)
    (hconn : G.Connected) :
    Nonempty (DeltaRhoPartition G δ (4 * (t - 1) * δ + 2) Set.univ (2 ^ (t - 2))) := by
  have heq : 4 * δ + 4 * (t - 2) * δ + 2 = 4 * (t - 1) * δ + 2 := by
    have h1 : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
    have h2 : t - 2 + 1 = t - 1 := by omega
    nlinarith [h1, h2]
  rw [← heq]
  apply region_step μ Set.univ t δ δ ht le_rfl hδ hconn
  constructor
  intro model
  apply hH
  exact ⟨model.bag, model.nonempty, model.connected, model.disjoint, model.adjacent⟩
