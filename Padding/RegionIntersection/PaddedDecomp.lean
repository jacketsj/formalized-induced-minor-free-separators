/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.SparseCover
import Padding.Defs.WeightedGraph
import Padding.PaddedDecompDefs
import Padding.Statements.RIGPaddedDecompDef
import Padding.RegionIntersection.WeightedMetricSpace
import Padding.RegionIntersection.WeightedSparseCover

/-! # Padded Decompositions on Vertex-Weighted Region Intersection Graphs

## Main Result

* `weighted_region_intersection_padded_decomp_explicit`: Vertex-weighted region intersection
  graphs over `Kₜ`-minor-free graphs admit padded decomposition schemes with simple
  `O(t^2), Ω(1/t)` parameters written directly in the theorem statement.
* `weighted_region_intersection_light_padded_decomp_explicit`: the endpoint-light variant,
  obtained by applying the same theorem to the half-weights.

## Proof Chain

1. `region_intersection_asymptotic_dimension`: each connected component of the grown-region
   graph `G^ρ` has a `(1, 4(t-1)+2)`-partition of size `2^{t-2}`.
2. The combined labelling of `G^ρ` (`WeightedLabeling`) yields, in the vertex-weighted
   metric, components of bounded diameter that are `ρ`-separated within each label class.
3. These components, enlarged, form a `(3(16(t-1)+9), 2^{t-2}+1)`-sparse cover scheme
   (`weighted_admits_sparse_cover_scheme`).
4. `sparse_cover_scheme_to_padded_decomp_scheme` (Conroy-Filtser) turns the sparse cover
   scheme into a padded decomposition scheme, and the final statement weakens those
   constants to `4096 * t^2` and `1 / (512 * t)`.

The vertex set is assumed finite (`Fintype V₁`), matching the finite-metric setting of the
source; this is needed so that the family of clusters at each scale is finite.
-/

open PaddedDecomposition SimpleGraph

noncomputable section

universe u

private lemma two_pow_add_one_le_two_pow {t : ℕ} (ht : 2 ≤ t) :
    (2 ^ (t - 2) + 1 : ℕ) ≤ 2 ^ t := by
  calc
    2 ^ (t - 2) + 1 ≤ 2 ^ (t - 2) + 2 ^ (t - 2) := by
      exact Nat.add_le_add_left Nat.one_le_two_pow _
    _ = 2 * 2 ^ (t - 2) := by ring
    _ ≤ 4 * 2 ^ (t - 2) := by
      exact Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ 2 * 2 ^ (t - 2) := by norm_num
    _ = 2 ^ (2 + (t - 2)) := by rw [pow_add]
    _ = 2 ^ t := by
      have h : 2 + (t - 2) = t := by omega
      rw [h]

private lemma log_sparse_overlap_le_minor_size {t : ℕ} (ht : 2 ≤ t) :
    Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) ≤ (t : ℝ) := by
  have hs_nat : (2 ^ (t - 2) + 1 : ℕ) ≤ 2 ^ t := two_pow_add_one_le_two_pow ht
  have hs_pos : 0 < (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) := by positivity
  have hs_le : (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) ≤ ((2 ^ t : ℕ) : ℝ) := by
    exact_mod_cast hs_nat
  have hlog_le : Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) ≤
      Real.log (((2 ^ t : ℕ) : ℝ)) :=
    Real.log_le_log hs_pos hs_le
  have hlog_pow : Real.log (((2 ^ t : ℕ) : ℝ)) = (t : ℝ) * Real.log 2 := by
    norm_num [Nat.cast_pow, Real.log_pow]
  rw [hlog_pow] at hlog_le
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9.le]
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  nlinarith

private lemma exact_rig_beta_le_simple {t : ℕ} (ht : 2 ≤ t) :
    4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) *
        (2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ))) ≤
      4096 * (t : ℝ) ^ 2 := by
  have htR : 1 ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  have htm1 : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.sub_le t 1
  have hB : (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) ≤ 75 * (t : ℝ) := by
    push_cast
    nlinarith
  have hlog : Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) ≤ (t : ℝ) :=
    log_sparse_overlap_le_minor_size ht
  have hfac : 2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) ≤ 4 * (t : ℝ) := by
    nlinarith
  have hfac_nonneg : 0 ≤ 2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) := by
    have hlog_nonneg := Real.log_natCast_nonneg (2 ^ (t - 2) + 1)
    nlinarith
  calc
    4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) *
        (2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)))
        ≤ 4 * (75 * (t : ℝ)) * (4 * (t : ℝ)) := by
          gcongr
    _ ≤ 4096 * (t : ℝ) ^ 2 := by nlinarith

private lemma simple_rig_delta_le_exact {t : ℕ} (ht : 2 ≤ t) :
    1 / (512 * (t : ℝ)) ≤
      1 / (4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ))) := by
  have htR : 1 ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  have htm1 : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.sub_le t 1
  have hB : (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) ≤ 75 * (t : ℝ) := by
    push_cast
    nlinarith
  have hBpos : 0 < (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) := by
    have : 0 < 3 * (16 * (t - 1) + 9) := by omega
    exact_mod_cast this
  have hden : 4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) ≤ 512 * (t : ℝ) := by
    nlinarith
  exact one_div_le_one_div_of_le (mul_pos (by norm_num) hBpos) hden

private lemma exact_rig_delta_nonneg {t : ℕ} :
    0 ≤ 1 / (4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ))) := by
  positivity

/-- **Main theorem (endpoint-heavy, explicit parameters).** Vertex-weighted connected region
intersection graphs over `Kₜ`-minor-free graphs admit a padded decomposition scheme with
simple `O(t^2), Ω(1/t)` parameters. -/
theorem weighted_region_intersection_padded_decomp_explicit
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    @AdmitsPaddedDecompScheme V₁ (G.weightedPseudoMetricSpace w hw hconn)
      (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ))) := by
  letI inst := G.weightedPseudoMetricSpace w hw hconn
  exact PaddedDecomposition.AdmitsPaddedDecompScheme.weaken
    (WeightedRIG.weighted_rig_admits_padded_explicit μ t ht hH w hw hconn)
    (exact_rig_beta_le_simple ht) (simple_rig_delta_le_exact ht) exact_rig_delta_nonneg

/-- **Main theorem (endpoint-light, explicit parameters).** This is the endpoint-heavy
theorem applied to the half-weights, so each edge contributes `(w u + w v) / 2`. -/
theorem weighted_region_intersection_light_padded_decomp_explicit
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    @AdmitsPaddedDecompScheme V₁
      (G.weightedPseudoMetricSpace (fun v => w v / 2)
        (fun v => div_nonneg (hw v) (by norm_num)) hconn)
      (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ))) :=
  weighted_region_intersection_padded_decomp_explicit μ t ht hH
    (fun v => w v / 2) (fun v => div_nonneg (hw v) (by norm_num)) hconn

/-- Existential wrapper around `weighted_region_intersection_padded_decomp_explicit`. -/
theorem weighted_region_intersection_padded_decomp
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    ∃ (β δ₀ : ℝ), 0 < β ∧ 0 < δ₀ ∧
      @AdmitsPaddedDecompScheme V₁ (G.weightedPseudoMetricSpace w hw hconn) β δ₀ :=
  ⟨4096 * (t : ℝ) ^ 2, 1 / (512 * (t : ℝ)), by positivity,
    one_div_pos.mpr (mul_pos (by norm_num) (by positivity)),
    weighted_region_intersection_padded_decomp_explicit μ t ht hH w hw hconn⟩

namespace RIGPadded

private def toImplementationModel {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) : _root_.RegionIntersectionModel G H where
  region := μ.region
  region_nonempty := μ.region_nonempty
  region_connected := μ.region_connected
  adj_intersect := μ.adj_intersect
  nonadj_disjoint := μ.nonadj_disjoint

private lemma toImplementationExcludes {V : Type u} {H : SimpleGraph V} {t : ℕ}
    (hH : ExcludesCompleteMinor H t) : _root_.SimpleGraph.ExcludesMinor H t := by
  intro hminor
  apply hH
  simpa [HasCompleteMinor, _root_.SimpleGraph.HasCompleteMinor] using hminor

private def ofImplementationPartition {X : Type u}
    (P : PaddedDecomposition.Partition X) : Partition X where
  label := P.label

@[simp] private lemma ofImplementationPartition_cluster {X : Type u}
    (P : PaddedDecomposition.Partition X) (z : X) :
    (ofImplementationPartition P).cluster z = P.cluster z :=
  rfl

private def ofMetricPaddedDecomp {X : Type u} [PseudoMetricSpace X] {β δ Δ : ℝ}
    (hΔ : 0 ≤ Δ) (pd : PaddedDecomposition.PaddedDecomp X β δ Δ) :
    PaddedDecomp X (fun x y => dist x y) β δ Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := fun ω => ofImplementationPartition (pd.partition ω)
  bounded := by
    intro ω z x y hx hy
    have hx' : x ∈ (pd.partition ω).cluster z := by
      simpa using hx
    have hy' : y ∈ (pd.partition ω).cluster z := by
      simpa using hy
    have hset_bdd : Bornology.IsBounded ((pd.partition ω).cluster z) :=
      Metric.isBounded_iff_ediam_ne_top.mpr
        (ne_of_lt (lt_of_le_of_lt ((pd.bounded ω) z) ENNReal.ofReal_lt_top))
    have hdist : dist x y ≤ Metric.diam ((pd.partition ω).cluster z) :=
      Metric.dist_le_diam_of_mem hset_bdd hx' hy'
    exact le_trans hdist
      (PaddedDecomposition.Partition.IsBounded.diam_le (pd.bounded ω) hΔ z)
  cluster_subset_measurable := by
    intro S z
    simpa using pd.cluster_subset_measurable S z
  padding := by
    intro γ hγ0 hγδ z
    simpa [closedBall] using pd.padding γ hγ0 hγδ z

private theorem ofMetricAdmits {X : Type u} [PseudoMetricSpace X] {β δ : ℝ}
    (h : PaddedDecomposition.AdmitsPaddedDecompScheme X β δ) :
    AdmitsPaddedDecompScheme X (fun x y => dist x y) β δ :=
  fun Δ hΔ => (h Δ hΔ).map (fun pd => ofMetricPaddedDecomp hΔ.le pd)

private def PaddedDecomp.weaken_beta {X : Type u} {d : X → X → ℝ}
    {β β' δ Δ : ℝ} (pd : PaddedDecomp X d β δ Δ) (hβ : β ≤ β') :
    PaddedDecomp X d β' δ Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := pd.partition
  bounded := pd.bounded
  cluster_subset_measurable := pd.cluster_subset_measurable
  padding := by
    intro γ hγ0 hγδ z
    calc
      ENNReal.ofReal (Real.exp (-β' * γ))
          ≤ ENNReal.ofReal (Real.exp (-β * γ)) := by
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp_of_le
            nlinarith
      _ ≤ pd.μ.toOuterMeasure
          {ω | closedBall d z (γ * Δ) ⊆ (pd.partition ω).cluster z} :=
            pd.padding γ hγ0 hγδ z

private def PaddedDecomp.weaken_delta {X : Type u} {d : X → X → ℝ}
    {β δ δ' Δ : ℝ} (pd : PaddedDecomp X d β δ Δ) (hδ : δ' ≤ δ) :
    PaddedDecomp X d β δ' Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := pd.partition
  bounded := pd.bounded
  cluster_subset_measurable := pd.cluster_subset_measurable
  padding := fun γ hγ0 hγδ' z => pd.padding γ hγ0 (le_trans hγδ' hδ) z

private theorem AdmitsPaddedDecompScheme.weaken {X : Type u} {d : X → X → ℝ}
    {β β' δ δ' : ℝ} (h : AdmitsPaddedDecompScheme X d β δ)
    (hβ : β ≤ β') (hδ : δ' ≤ δ) :
    AdmitsPaddedDecompScheme X d β' δ' :=
  fun Δ hΔ => (h Δ hΔ).map (fun pd => (pd.weaken_beta hβ).weaken_delta hδ)

private lemma endpointLightWalkLength_eq_edgeWeightSum_half
    {V : Type u} {G : SimpleGraph V} (w : V → ℝ) {x y : V} (p : G.Walk x y) :
    endpointLightWalkLength w p =
      _root_.SimpleGraph.Walk.edgeWeightSum p (fun v => w v / 2) := by
  induction p with
  | nil =>
      simp [endpointLightWalkLength, _root_.SimpleGraph.Walk.edgeWeightSum]
  | @cons u v z huv p ih =>
      simp [endpointLightWalkLength, _root_.SimpleGraph.Walk.edgeWeightSum]
      ring_nf

@[simp] private lemma endpointLightWalkLength_nil
    {V : Type u} {G : SimpleGraph V} (w : V → ℝ) (x : V) :
    endpointLightWalkLength w (SimpleGraph.Walk.nil : G.Walk x x) = 0 := by
  simp [endpointLightWalkLength]

@[simp] private lemma endpointLightWalkLength_cons
    {V : Type u} {G : SimpleGraph V} (w : V → ℝ)
    {x y z : V} (hxy : G.Adj x y) (p : G.Walk y z) :
    endpointLightWalkLength w (SimpleGraph.Walk.cons hxy p) =
      (w x + w y) / 2 + endpointLightWalkLength w p := by
  simp [endpointLightWalkLength]

@[simp] private lemma endpointHeavyWalkLength_nil
    {V : Type u} {G : SimpleGraph V} (w : V → ℝ) (x : V) :
    endpointHeavyWalkLength w (SimpleGraph.Walk.nil : G.Walk x x) = w x := by
  simp [endpointHeavyWalkLength]

@[simp] private lemma endpointHeavyWalkLength_cons
    {V : Type u} {G : SimpleGraph V} (w : V → ℝ)
    {x y z : V} (hxy : G.Adj x y) (p : G.Walk y z) :
    endpointHeavyWalkLength w (SimpleGraph.Walk.cons hxy p) =
      w x + endpointHeavyWalkLength w p := by
  simp [endpointHeavyWalkLength]

private lemma endpointLightWalkLength_nonneg {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) :
    0 ≤ endpointLightWalkLength w p := by
  induction p with
  | nil => simp
  | @cons u v z huv p ih =>
      rw [endpointLightWalkLength_cons]
      nlinarith [hw u, hw v, ih]

private lemma endpointHeavyWalkLength_nonneg {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) :
    0 ≤ endpointHeavyWalkLength w p := by
  induction p with
  | nil => simp [hw _]
  | @cons u v z huv p ih =>
      rw [endpointHeavyWalkLength_cons]
      nlinarith [hw u, ih]

private lemma endpointLightDist_bddBelow {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x y : V) :
    BddBelow (Set.range fun p : G.Walk x y => endpointLightWalkLength w p) := by
  exact ⟨0, Set.forall_mem_range.2 fun p => endpointLightWalkLength_nonneg hw p⟩

private lemma endpointHeavyDist_bddBelow {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x y : V) :
    BddBelow (Set.range fun p : G.Walk x y => endpointHeavyWalkLength w p) := by
  exact ⟨0, Set.forall_mem_range.2 fun p => endpointHeavyWalkLength_nonneg hw p⟩

private lemma endpointLightDist_le_walk {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) :
    endpointLightDist G w x y ≤ endpointLightWalkLength w p := by
  apply ciInf_le
  exact endpointLightDist_bddBelow hw x y

private lemma endpointHeavyDist_le_walk_of_ne {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {x y : V} (hne : x ≠ y) (p : G.Walk x y) :
    endpointHeavyDist G w x y ≤ endpointHeavyWalkLength w p := by
  simp [endpointHeavyDist, hne]
  apply ciInf_le
  exact endpointHeavyDist_bddBelow hw x y

private lemma endpointLightDist_nonneg {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x y : V) :
    0 ≤ endpointLightDist G w x y := by
  exact Real.iInf_nonneg fun p => endpointLightWalkLength_nonneg hw p

private lemma endpointLightDist_self {V : Type u} {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x : V) :
    endpointLightDist G w x x = 0 := by
  refine le_antisymm (endpointLightDist_le_walk hw SimpleGraph.Walk.nil) ?_
  exact endpointLightDist_nonneg hw x x

private lemma endpointLightWalkLength_add_half_start_le_heavy
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x y : V} (p : G.Walk x y) :
    endpointLightWalkLength w p + w x / 2 ≤ endpointHeavyWalkLength w p := by
  induction p with
  | @nil a =>
      simp
      nlinarith [hw a]
  | @cons u v z huv p ih =>
      rw [endpointLightWalkLength_cons, endpointHeavyWalkLength_cons]
      nlinarith [ih]

private lemma endpointLightWalkLength_le_endpointHeavyWalkLength
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x y : V} (p : G.Walk x y) :
    endpointLightWalkLength w p ≤ endpointHeavyWalkLength w p := by
  have h := endpointLightWalkLength_add_half_start_le_heavy hw p
  nlinarith [hw x]

private lemma endpointHeavyWalkLength_le_start_add_two_endpointLightWalkLength
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x y : V} (p : G.Walk x y) :
    endpointHeavyWalkLength w p ≤ w x + 2 * endpointLightWalkLength w p := by
  induction p with
  | nil => simp
  | @cons u v z huv p ih =>
      rw [endpointLightWalkLength_cons, endpointHeavyWalkLength_cons]
      nlinarith [ih, hw u]

private lemma endpointHeavyWalkLength_le_two_endpointLightWalkLength_of_ne
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) (hne : x ≠ y) :
    endpointHeavyWalkLength w p ≤ 2 * endpointLightWalkLength w p := by
  cases p with
  | nil => contradiction
  | @cons u v z huv p =>
      have h := endpointHeavyWalkLength_le_start_add_two_endpointLightWalkLength
        (w := w) hw p
      rw [endpointLightWalkLength_cons, endpointHeavyWalkLength_cons]
      nlinarith [h]

private lemma endpointLightDist_le_endpointHeavyDist
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) (x y : V) :
    endpointLightDist G w x y ≤ endpointHeavyDist G w x y := by
  by_cases hxy : x = y
  · subst y
    rw [endpointLightDist_self hw]
    simp [endpointHeavyDist]
  · simp [endpointHeavyDist, hxy]
    haveI : Nonempty (G.Walk x y) := ⟨Classical.choice (hconn x y)⟩
    apply le_ciInf
    intro p
    exact le_trans (endpointLightDist_le_walk hw p)
      (endpointLightWalkLength_le_endpointHeavyWalkLength hw p)

private lemma endpointHeavyDist_le_two_endpointLightDist
    {V : Type u} {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) (x y : V) :
    endpointHeavyDist G w x y ≤ 2 * endpointLightDist G w x y := by
  by_cases hxy : x = y
  · subst y
    simp [endpointHeavyDist]
    nlinarith [endpointLightDist_nonneg (G := G) hw x x]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hnonempty : Set.Nonempty
        (Set.range fun p : G.Walk x y => endpointLightWalkLength w p) :=
      ⟨_, ⟨Classical.choice (hconn x y), rfl⟩⟩
    obtain ⟨_, hp, hplt⟩ := exists_lt_of_csInf_lt hnonempty
      (lt_add_of_pos_right (endpointLightDist G w x y) (half_pos hε))
    obtain ⟨p, rfl⟩ := hp
    have hheavy_walk := endpointHeavyDist_le_walk_of_ne hw hxy p
    have hwalk := endpointHeavyWalkLength_le_two_endpointLightWalkLength_of_ne
      (w := w) hw p hxy
    nlinarith

private def endpointLightToEndpointHeavyPaddedDecomp {X : Type u} {dL dH : X → X → ℝ}
    (hL_le_H : ∀ x y, dL x y ≤ dH x y)
    (hH_le_twoL : ∀ x y, dH x y ≤ 2 * dL x y)
    {β δ Δ : ℝ} (pd : PaddedDecomp X dL β δ (Δ / 2)) :
    PaddedDecomp X dH (2 * β) (δ / 2) Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := pd.partition
  bounded := by
    intro ω z x y hx hy
    have hL := pd.bounded ω z x y hx hy
    have hH := hH_le_twoL x y
    nlinarith
  cluster_subset_measurable := pd.cluster_subset_measurable
  padding := by
    intro γ hγ0 hγδ z
    let lightEvent :=
      {ω | closedBall dL z ((2 * γ) * (Δ / 2)) ⊆ (pd.partition ω).cluster z}
    let heavyEvent :=
      {ω | closedBall dH z (γ * Δ) ⊆ (pd.partition ω).cluster z}
    have hlight : pd.μ.toOuterMeasure lightEvent ≥
        ENNReal.ofReal (Real.exp (-β * (2 * γ))) := by
      exact pd.padding (2 * γ) (by nlinarith) (by nlinarith) z
    have hsubset : lightEvent ⊆ heavyEvent := by
      intro ω hω x hx
      apply hω
      have hx' : dL x z ≤ γ * Δ := le_trans (hL_le_H x z) (by simpa [closedBall] using hx)
      simpa [closedBall] using (show dL x z ≤ (2 * γ) * (Δ / 2) from by nlinarith)
    calc
      ENNReal.ofReal (Real.exp (-(2 * β) * γ))
          = ENNReal.ofReal (Real.exp (-β * (2 * γ))) := by ring_nf
      _ ≤ pd.μ.toOuterMeasure lightEvent := hlight
      _ ≤ pd.μ.toOuterMeasure heavyEvent := by
        exact (pd.μ.toOuterMeasure).mono hsubset

private theorem endpointLightAdmitsToEndpointHeavy {X : Type u} {dL dH : X → X → ℝ}
    (hL_le_H : ∀ x y, dL x y ≤ dH x y)
    (hH_le_twoL : ∀ x y, dH x y ≤ 2 * dL x y)
    {β δ : ℝ} (h : AdmitsPaddedDecompScheme X dL β δ) :
    AdmitsPaddedDecompScheme X dH (2 * β) (δ / 2) :=
  fun Δ hΔ => (h (Δ / 2) (half_pos hΔ)).map
    (endpointLightToEndpointHeavyPaddedDecomp hL_le_H hH_le_twoL)

private theorem weighted_region_intersection_light_padded_decomp_exact
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : ExcludesCompleteMinor H t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    AdmitsPaddedDecompScheme V₁ (endpointLightDist G w)
      (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ))) := by
  let μ' : _root_.RegionIntersectionModel G H := toImplementationModel μ
  have hmetric :
      @PaddedDecomposition.AdmitsPaddedDecompScheme V₁
        (G.weightedPseudoMetricSpace (fun v => w v / 2)
          (fun v => div_nonneg (hw v) (by norm_num)) hconn)
        (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ))) :=
    _root_.weighted_region_intersection_light_padded_decomp_explicit
      μ' t ht (toImplementationExcludes hH) w hw hconn
  letI := G.weightedPseudoMetricSpace (fun v => w v / 2)
    (fun v => div_nonneg (hw v) (by norm_num)) hconn
  have hdist :
      AdmitsPaddedDecompScheme V₁
        (fun x y => _root_.SimpleGraph.weightedDist G (fun v => w v / 2) x y)
        (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ))) :=
    ofMetricAdmits hmetric
  change AdmitsPaddedDecompScheme V₁
      (fun x y => ⨅ p : G.Walk x y, endpointLightWalkLength w p)
      (4096 * (t : ℝ) ^ 2) (1 / (512 * (t : ℝ)))
  simpa [endpointLightWalkLength_eq_edgeWeightSum_half,
    _root_.SimpleGraph.weightedDist] using hdist

/-- Public endpoint-light statement, with relaxed constants. -/
theorem weighted_region_intersection_light_padded_decomp_explicit
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : ExcludesCompleteMinor H t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    AdmitsPaddedDecompScheme V₁ (endpointLightDist G w)
      (8192 * (t : ℝ) ^ 2) (1 / (1024 * (t : ℝ))) := by
  have hβ : 4096 * (t : ℝ) ^ 2 ≤ 8192 * (t : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (t : ℝ)]
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) ht)
  have hδ : 1 / (1024 * (t : ℝ)) ≤ 1 / (512 * (t : ℝ)) := by
    have hden : 512 * (t : ℝ) ≤ 1024 * (t : ℝ) := by nlinarith
    exact one_div_le_one_div_of_le (mul_pos (by norm_num) htpos) hden
  exact AdmitsPaddedDecompScheme.weaken
    (weighted_region_intersection_light_padded_decomp_exact μ t ht hH w hw hconn) hβ hδ

/-- Public endpoint-heavy statement, using path vertex-weight sums. -/
theorem weighted_region_intersection_padded_decomp_explicit
    {V₁ V₂ : Type u} [Fintype V₁]
    {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : ExcludesCompleteMinor H t) (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    AdmitsPaddedDecompScheme V₁ (endpointHeavyDist G w)
      (8192 * (t : ℝ) ^ 2) (1 / (1024 * (t : ℝ))) := by
  have hlight :=
    weighted_region_intersection_light_padded_decomp_exact μ t ht hH w hw hconn
  have hheavy :=
    endpointLightAdmitsToEndpointHeavy
      (endpointLightDist_le_endpointHeavyDist (G := G) hw hconn)
      (endpointHeavyDist_le_two_endpointLightDist (G := G) hw hconn)
      hlight
  convert hheavy using 1 <;> ring

end RIGPadded

end
