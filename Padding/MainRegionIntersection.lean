/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.RIGPaddedDecompDef
import Padding.RegionIntersection.PaddedDecomp

/-! # Main Result 3 — Padded decompositions for region intersection graphs
(independent entry point)

This file states the **padded decomposition theorem for region intersection graphs**
in isolation, with simple constants written directly in the theorem statement.

## Verifier-facing files

To verify the statement surface, read these two whole files:

* `Padding/Statements/RIGPaddedDecompDef.lean`;
* this file.

The theorem below is stated directly for the explicit endpoint-light and endpoint-heavy
vertex-weighted shortest-path distances, not for a bundled pseudometric instance.  The
import of `Padding.RegionIntersection.PaddedDecomp` supplies the checked proof term only;
it is not part of the statement-verification surface.
-/

open SimpleGraph

universe u

namespace MainResults

/-- **Padded decompositions for region intersection graphs.** Given a region intersection
model of a connected graph `G` over a `Kₜ`-minor-free host `H` (`t ≥ 2`) and nonnegative
vertex weights `w`, both the endpoint-light and endpoint-heavy vertex-weighted
shortest-path distances admit `(8192 t^2, 1/(1024t))`-padded decomposition schemes, in the
explicit-distance sense defined in `RIGPadded`.

This is the closest Lean-facing form of Theorem 6.6 without the string-graph corollary,
with relaxed constants that keep the same `O(t^2), Ω(1/t)` asymptotic dependence. -/
theorem rig_padded_decomposition_schemes
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RIGPadded.RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : RIGPadded.ExcludesCompleteMinor H t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    RIGPadded.AdmitsPaddedDecompScheme V₁
      (RIGPadded.endpointLightDist G w)
      (8192 * (t : ℝ) ^ 2) (1 / (1024 * (t : ℝ))) ∧
    RIGPadded.AdmitsPaddedDecompScheme V₁ (RIGPadded.endpointHeavyDist G w)
      (8192 * (t : ℝ) ^ 2) (1 / (1024 * (t : ℝ))) :=
  ⟨RIGPadded.weighted_region_intersection_light_padded_decomp_explicit μ t ht hH w hw hconn,
    RIGPadded.weighted_region_intersection_padded_decomp_explicit μ t ht hH w hw hconn⟩

end MainResults

#print axioms MainResults.rig_padded_decomposition_schemes
