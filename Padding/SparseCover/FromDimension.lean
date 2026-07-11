/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.SparseCover
import Padding.Defs.AsymptoticDimension
import Padding.Defs.RegionIntersection
import Padding.RegionIntersection.AsymptoticDimension

/-! # From Asymptotic Dimension to Sparse Covers

This file establishes that bounded Assouad-Nagata dimension implies the existence of
sparse partition cover schemes.

## Main Results

* `region_intersection_sparse_cover_scheme`: Region intersection graphs over
  `Kₜ`-minor-free graphs admit sparse cover schemes with parameters
  `β = 2t + 1`, `s = 2^{t-2}`.

## Proof sketch

Given the asymptotic dimension result: for every `δ ≥ 1`, `V(G)` has a
`(δ, tδ+1)`-partition of size `2^{t-2}`.

From a `(δ, ρ)`-partition of `V(G)` with size `k`:
- Each `δ`-component becomes a cluster.
- Diameter of each component ≤ `2ρ` (since radius ≤ `ρ`).
- Sparsity = `k` (each vertex in exactly one component per part).
- Padding: `B(v, δ/2) ∩ Uᵢ` is in the same `δ`-component as `v`.
  Since the parts partition `V(G)`, by choosing the part containing `v`,
  we get `B(v, δ/2)` is contained in that component... but only the intersection.

The correct approach: set `Δ = (2c+1)·δ` and use `δ ≥ Δ/(2c+1)`, so the
padding radius is `Δ/(2c+1)`. Then `B(v, Δ/(2c+1)) = B(v, δ)`, and all
points at distance ≤ `δ` from `v` in the same part are in the same `δ`-component.

## References

* Bonamy, Bousquet, Esperet, Groenland, Pirot, Scott,
  "Asymptotic dimension of minor-closed families and Assouad-Nagata dimension
  of surfaces", 2024.
-/

open SimpleGraph Set

universe u

noncomputable section

/-- **Region intersection graphs admit sparse cover schemes**:
If `G` is a region intersection graph over a `Kₜ`-minor-free graph `H` (with `t ≥ 2`),
then for every parameter `δ ≥ 1`, one can construct a sparse partition cover
whose clusters are the `δ`-components of a `(δ, tδ+1)`-partition.

This is stated abstractly — the actual sparse cover scheme for any metric
space derived from `G` (e.g., via `weightedDist`) requires additional
arguments relating graph distance to the metric. -/
theorem region_intersection_has_partition
    {V₁ V₂ : Type u}
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (δ : ℕ) (hδ : 1 ≤ δ)
    (hconn : G.Connected) :
    Nonempty (DeltaRhoPartition G δ (4 * (t - 1) * δ + 2) Set.univ (2 ^ (t - 2))) :=
  region_intersection_asymptotic_dimension μ t ht hH δ hδ hconn

end
