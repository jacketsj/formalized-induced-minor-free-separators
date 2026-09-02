/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.SparseCover
import Padding.PaddedDecompDefs
import Padding.SparseCover.PaddingProof
import Padding.SparseCover.TruncatedExponential
import Padding.SparseCover.PaddingBound
import Padding.SparseCover.FubiniHelper
import Mathlib

/-! # Measure-theoretic core of the sparse cover → padded decomposition proof

This file contains the construction of the random partition from a sparse cover and the
analysis of its padding probability, following `ConroyFiltserProof.tex`.
-/

open MeasureTheory Metric Set Real PaddedDecomposition Classical

noncomputable section

/-! ## Score function and padding claim -/

/-- The score function `f_C(v) = δ_C · (Δ/β) + d(v, Cᶜ)`. -/
def sparseF {X : Type*} [PseudoMetricSpace X]
    (C : Set X) (δ_C : ℝ) (Δ β : ℝ) (v : X) : ℝ :=
  δ_C * (Δ / β) + Metric.infDist v Cᶜ

lemma sparseF_le_of_nmem {X : Type*} [PseudoMetricSpace X]
    {C : Set X} {v : X} (hv : v ∉ C) (δ_C Δ β : ℝ) :
    sparseF C δ_C Δ β v ≤ δ_C * (Δ / β) := by
  simp [sparseF, Metric.infDist_zero_of_mem (mem_compl hv)]

lemma padding_claim {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Fintype ι]
    (clusters : ι → Set X) (δ_vals : ι → ℝ) (Δ β : ℝ)
    (v : X) (C_idx : ι) (r : ℝ)
    (hgap : ∀ j : ι, j ≠ C_idx →
      sparseF (clusters C_idx) (δ_vals C_idx) Δ β v >
      sparseF (clusters j) (δ_vals j) Δ β v + 2 * r) :
    ∀ u ∈ Metric.closedBall v r,
      ∀ j : ι, j ≠ C_idx →
        sparseF (clusters C_idx) (δ_vals C_idx) Δ β u >
        sparseF (clusters j) (δ_vals j) Δ β u := by
  intro u hu j hj
  have h1 : Metric.infDist u (clusters C_idx)ᶜ ≥
      Metric.infDist v (clusters C_idx)ᶜ - dist u v := by
    linarith [infDist_le_infDist_add_dist (x := v) (y := u) (s := (clusters C_idx)ᶜ),
              dist_comm u v]
  have h2 : Metric.infDist u (clusters j)ᶜ ≤
      Metric.infDist v (clusters j)ᶜ + dist u v :=
    infDist_le_infDist_add_dist
  unfold sparseF at *
  linarith [hgap j hj, show dist u v ≤ r from hu]

/-! ## Partition Construction -/

def bestContainingCluster {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (v : X) (hv : ∃ i : Fin n, v ∈ clusters i) : Fin n :=
  let containing := Finset.univ.filter (fun i : Fin n => v ∈ clusters i)
  let h_ne : containing.Nonempty := by
    exact Finset.filter_nonempty_iff.mpr ⟨hv.choose, Finset.mem_univ _, hv.choose_spec⟩
  let score := fun i : Fin n => sparseF (clusters i) (δ i) Δ β v
  let maxScore := containing.sup' h_ne score
  (containing.filter (fun i => score i = maxScore)).min'
    (by
      obtain ⟨i, hi, hi_eq⟩ := Finset.exists_mem_eq_sup' h_ne score
      exact Finset.filter_nonempty_iff.mpr ⟨i, hi, hi_eq.symm⟩)

lemma bestContainingCluster_mem {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (v : X) (hv : ∃ i : Fin n, v ∈ clusters i) :
    v ∈ clusters (bestContainingCluster clusters δ Δ β v hv) := by
  have := Finset.min'_mem ( Finset.filter ( fun i => sparseF ( clusters i ) ( δ i ) Δ β v = Finset.sup' ( Finset.filter ( fun i => v ∈ clusters i ) Finset.univ ) ( Finset.filter_nonempty_iff.mpr ⟨ hv.choose, Finset.mem_univ _, hv.choose_spec ⟩ ) fun i => sparseF ( clusters i ) ( δ i ) Δ β v ) ( Finset.filter ( fun i => v ∈ clusters i ) Finset.univ ) )
  grind +locals

lemma bestContainingCluster_best {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (v : X) (hv : ∃ i : Fin n, v ∈ clusters i) (j : Fin n) (hj : v ∈ clusters j) :
    sparseF (clusters (bestContainingCluster clusters δ Δ β v hv))
      (δ (bestContainingCluster clusters δ Δ β v hv)) Δ β v ≥
    sparseF (clusters j) (δ j) Δ β v := by
  have h_score_le : ∀ i ∈ Finset.univ.filter (fun i => v ∈ clusters i), sparseF (clusters i) (δ i) Δ β v ≤ Finset.sup' (Finset.univ.filter (fun i => v ∈ clusters i)) (by
  exact ⟨ j, by simpa using hj ⟩) (fun i => sparseF (clusters i) (δ i) Δ β v) := by
    exact fun i hi => Finset.le_sup' ( fun i => sparseF ( clusters i ) ( δ i ) Δ β v ) hi
  generalize_proofs at *;
  convert h_score_le j ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj ⟩ ) |> le_trans <| ?_ using 1
  generalize_proofs at *;
  unfold bestContainingCluster;
  simp +zetaDelta at *;
  intro i hi; have := Finset.min'_mem ( Finset.filter ( fun i => sparseF ( clusters i ) ( δ i ) Δ β v = Finset.sup' ( Finset.filter ( fun i => v ∈ clusters i ) Finset.univ ) ( by tauto ) fun i => sparseF ( clusters i ) ( δ i ) Δ β v ) ( Finset.filter ( fun i => v ∈ clusters i ) Finset.univ ) ) ( by
    exact Exists.elim ( Finset.exists_mem_eq_sup' ‹_› fun i => sparseF ( clusters i ) ( δ i ) Δ β v ) fun i hi => ⟨ i, by aesop ⟩ ) ; aesop;

def scPartition {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i) : Partition X where
  label v := (bestContainingCluster clusters δ Δ β v (hcover v)).val

lemma scPartition_cluster_subset {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i) (z : X) :
    (scPartition clusters δ Δ β hcover).cluster z ⊆
    clusters (bestContainingCluster clusters δ Δ β z (hcover z)) := by
  intro w hw
  have h_eq : bestContainingCluster clusters δ Δ β w (hcover w) = bestContainingCluster clusters δ Δ β z (hcover z) := by
    exact Fin.val_injective hw;
  exact h_eq ▸ bestContainingCluster_mem clusters δ Δ β w ( hcover w )

lemma scPartition_bounded {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} (clusters : Fin n → Set X) (δ : Fin n → ℝ) (Δ β : ℝ)
    (hediam : ∀ i, Metric.ediam (clusters i) ≤ ENNReal.ofReal Δ)
    (hcover : ∀ v : X, ∃ i, v ∈ clusters i) :
    (scPartition clusters δ Δ β hcover).IsBounded Δ := by
  intro z
  exact le_trans (Metric.ediam_mono (scPartition_cluster_subset clusters δ Δ β hcover z))
    (hediam _)

lemma ediam_le_of_diam_le_of_bounded {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {Δ : ℝ}
    (hdiam : Metric.diam S ≤ Δ)
    (hbdd : Bornology.IsBounded S) :
    Metric.ediam S ≤ ENNReal.ofReal Δ := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  exact le_trans (Metric.dist_le_diam_of_mem hbdd hx hy) hdiam

/-! ## The score threshold

For a cluster `i`, `scThreshold` is the minimal value of the offset `o i` such that, above
it, cluster `i` becomes the strict maximizer of the score at `z`. -/

def scThreshold {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X) (i : Fin n) : ℝ :=
  (insert (0 : ℝ)
    ((Finset.univ.erase i).image
      (fun j => (β / Δ) *
        (sparseF (clusters j) (o j) Δ β z - Metric.infDist z (clusters i)ᶜ)))).sup'
    (Finset.insert_nonempty _ _) id

lemma scThreshold_nonneg {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X) (i : Fin n) :
    0 ≤ scThreshold clusters o Δ β z i := by
  unfold scThreshold
  exact Finset.le_sup' id (Finset.mem_insert_self _ _)

lemma scThreshold_ge {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X) (i j : Fin n) (hj : j ≠ i) :
    (β / Δ) * (sparseF (clusters j) (o j) Δ β z - Metric.infDist z (clusters i)ᶜ)
      ≤ scThreshold clusters o Δ β z i := by
  unfold scThreshold
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image_of_mem
  exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩

lemma scThreshold_congr {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o o' : Fin n → ℝ) (Δ β : ℝ) (z : X) (i : Fin n)
    (h : ∀ j, j ≠ i → o j = o' j) :
    scThreshold clusters o Δ β z i = scThreshold clusters o' Δ β z i := by
  unfold scThreshold;
  congr! 2;
  exact Finset.image_congr fun j hj => by aesop;

/-! ## Metric lemmas about the best cluster and the threshold -/

lemma infDist_compl_ge {X : Type*} [PseudoMetricSpace X]
    {C : Set X} {v : X} {r : ℝ} (hne : Cᶜ.Nonempty)
    (hsub : Metric.closedBall v r ⊆ C) :
    r ≤ Metric.infDist v Cᶜ := by
  have h_point : ∀ w ∈ Cᶜ, r ≤ dist v w := by
    exact fun w hw => not_lt.1 fun hlt => hw <| hsub <| Metric.mem_closedBall'.2 hlt.le;
  exact (le_infDist hne).mpr h_point

lemma sparseF_gt_of_gt_threshold {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X) (i j : Fin n)
    (hΔ : 0 < Δ) (hβ : 0 < β) (hj : j ≠ i)
    (h : scThreshold clusters o Δ β z i < o i) :
    sparseF (clusters j) (o j) Δ β z < sparseF (clusters i) (o i) Δ β z := by
  have h_mul : sparseF (clusters j) (o j) Δ β z - Metric.infDist z (clusters i)ᶜ < o i * (Δ / β) := by
    convert mul_lt_mul_of_pos_right ( lt_of_le_of_lt ( scThreshold_ge clusters o Δ β z i j hj ) h ) ( div_pos hΔ hβ ) using 1 ; ring_nf;
    simp +decide [ hΔ.ne', hβ.ne' ];
  unfold sparseF at *; linarith;

lemma best_eq_of_gt_threshold {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X) (i : Fin n)
    (hΔ : 0 < Δ) (hβ : 0 < β) (hzi : z ∈ clusters i)
    (h : scThreshold clusters o Δ β z i < o i)
    (hv : ∃ k : Fin n, z ∈ clusters k) :
    bestContainingCluster clusters o Δ β z hv = i := by
  apply Classical.byContradiction
  intro h_contra;
  exact absurd ( sparseF_gt_of_gt_threshold clusters o Δ β z i ( bestContainingCluster clusters o Δ β z hv ) hΔ hβ ( by tauto ) h ) ( by linarith [ bestContainingCluster_best clusters o Δ β z hv i hzi ] )

lemma best_score_ge {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β) (ho0 : ∀ k, 0 ≤ o k)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hv : ∃ k : Fin n, z ∈ clusters k) :
    Δ / β ≤ sparseF (clusters (bestContainingCluster clusters o Δ β z hv))
      (o (bestContainingCluster clusters o Δ β z hv)) Δ β z := by
  obtain ⟨ k, hk ⟩ := hpad z;
  refine' le_trans _ ( bestContainingCluster_best clusters o Δ β z hv k _ );
  · exact le_add_of_nonneg_of_le ( mul_nonneg ( ho0 k ) ( div_nonneg hΔ.le hβ.le ) ) ( infDist_compl_ge ( hcompl k ) hk );
  · exact hk ( Metric.mem_closedBall_self ( by positivity ) )

lemma off_ge_threshold_of_best {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β) (ho0 : ∀ k, 0 ≤ o k) (ho1 : ∀ k, o k ≤ 1)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (i : Fin n) (hbest : bestContainingCluster clusters o Δ β z (hcover z) = i) :
    scThreshold clusters o Δ β z i ≤ o i := by
  refine' Finset.sup'_le _ _ _;
  simp +zetaDelta at *;
  refine' ⟨ ho0 i, fun j hj => _ ⟩
  by_cases hj' : z ∈ clusters j
  · have h_le : sparseF (clusters j) (o j) Δ β z ≤ sparseF (clusters i) (o i) Δ β z := by
      have := bestContainingCluster_best clusters o Δ β z ( hcover z ) j hj'; aesop;
    unfold sparseF at *; field_simp at *; nlinarith [ ho0 i, ho1 i, ho0 j, ho1 j ] ;
  · have h_zero : Metric.infDist z (clusters j)ᶜ = 0 := by
      exact Metric.infDist_zero_of_mem ( by simpa )
    have h_le : sparseF (clusters i) (o i) Δ β z ≥ Δ / β := by
      have := best_score_ge clusters o Δ β z hΔ hβ ho0 hpad hcompl ( hcover z ) ; aesop;
    unfold sparseF at *;
    field_simp at *;
    nlinarith [ ho0 j, ho1 j ]

lemma best_eq_of_strict_max_pt {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (u : X)
    (hΔ : 0 < Δ) (hβ : 0 < β) (ho0 : ∀ k, 0 ≤ o k) (ho1 : ∀ k, o k ≤ 1)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (i : Fin n)
    (hstrict : ∀ j, j ≠ i →
      sparseF (clusters j) (o j) Δ β u < sparseF (clusters i) (o i) Δ β u) :
    bestContainingCluster clusters o Δ β u (hcover u) = i := by
  apply Classical.byContradiction
  intro h_contra;
  exact absurd ( bestContainingCluster_best clusters o Δ β u ( hcover u ) i ( (by
  by_cases hu : u ∈ clusters i;
  · exact hu;
  · obtain ⟨ k, hk ⟩ := hpad u
    have hk_ne_i : k ≠ i := by
      exact fun h => hu <| h ▸ hk ( Metric.mem_closedBall_self <| by positivity )
    have h_infDist : Metric.infDist u (clusters k)ᶜ ≥ Δ / β := by
      apply infDist_compl_ge (hcompl k) hk
    have h_sparseF_k : sparseF (clusters k) (o k) Δ β u ≥ Δ / β := by
      exact le_add_of_nonneg_of_le ( mul_nonneg ( ho0 k ) ( div_nonneg hΔ.le hβ.le ) ) h_infDist
    have h_sparseF_i : sparseF (clusters i) (o i) Δ β u ≤ Δ / β := by
      unfold sparseF at *; simp_all +decide [ div_eq_mul_inv, mul_left_comm ] ;
      rw [ Metric.infDist_zero_of_mem ( show u ∈ ( clusters i ) ᶜ from by simpa using hu ) ] ; nlinarith [ ho0 i, ho1 i, mul_inv_cancel_left₀ hβ.ne' Δ ]
    have h_contra : sparseF (clusters k) (o k) Δ β u < sparseF (clusters i) (o i) Δ β u := by
      exact hstrict k hk_ne_i
    linarith [h_sparseF_k, h_sparseF_i]) ) ) ( by linarith [ hstrict ( bestContainingCluster clusters o Δ β u ( hcover u ) ) h_contra ] )

lemma padding_from_off_gt {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β) (ho0 : ∀ k, 0 ≤ o k) (ho1 : ∀ k, o k ≤ 1)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (i : Fin n) (hzi : z ∈ clusters i) (gam : ℝ) (hgam0 : 0 ≤ gam)
    (h : scThreshold clusters o Δ β z i + 2 * gam < o i) :
    Metric.closedBall z (gam * (Δ / β)) ⊆ (scPartition clusters o Δ β hcover).cluster z := by
  intro u hu
  have hbest : bestContainingCluster clusters o Δ β u (hcover u) = i := by
    apply best_eq_of_strict_max_pt clusters o Δ β u hΔ hβ ho0 ho1 hpad hcompl hcover i (fun j hj => by
      apply padding_claim clusters o Δ β z i (gam * (Δ / β)) (fun j hj => by
        have := scThreshold_ge clusters o Δ β z i j hj;
        unfold sparseF at *; field_simp at *; nlinarith [ mul_inv_cancel_left₀ hβ.ne' Δ, mul_inv_cancel_left₀ hΔ.ne' β, mul_inv_cancel₀ hβ.ne', mul_inv_cancel₀ hΔ.ne', ho0 i, ho1 i, ho0 j, ho1 j ] ;) u hu j hj)
  have hbest_z : bestContainingCluster clusters o Δ β z (hcover z) = i := by
    apply best_eq_of_gt_threshold clusters o Δ β z i hΔ hβ hzi (by linarith) (hcover z)
  have hlabel : (scPartition clusters o Δ β hcover).label u = (scPartition clusters o Δ β hcover).label z := by
    unfold scPartition; aesop;
  exact (Partition.cluster_symm (scPartition clusters o Δ β hcover) z u).mp (id (Eq.symm hlabel))

lemma bad_imp_mem_Qbar {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (o : Fin n → ℝ) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β) (ho0 : ∀ k, 0 ≤ o k) (ho1 : ∀ k, o k ≤ 1)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (gam : ℝ) (hgam0 : 0 ≤ gam)
    (hbad : ¬ (Metric.closedBall z (gam * (Δ / β)) ⊆
      (scPartition clusters o Δ β hcover).cluster z)) :
    ∃ i : Fin n, z ∈ clusters i ∧
      scThreshold clusters o Δ β z i ≤ o i ∧
      o i ≤ scThreshold clusters o Δ β z i + 2 * gam := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, z ∈ clusters i ∧ scThreshold clusters o Δ β z i ≤ o i := by
    exact ⟨ _, bestContainingCluster_mem clusters o Δ β z ( hcover z ), off_ge_threshold_of_best clusters o Δ β z hΔ hβ ho0 ho1 hpad hcompl hcover _ rfl ⟩;
  contrapose! hbad;
  exact padding_from_off_gt clusters o Δ β z hΔ hβ ho0 ho1 hpad hcompl hcover i hi.1 gam hgam0 ( hbad i hi.1 hi.2 )

/-! ## The clamped offset and the cut/win events -/

/-- The clamped offset: clamp the raw sample into `[0,1]`. -/
def scOffset {n : ℕ} (ω : Fin n → ℝ) : Fin n → ℝ := fun k => max 0 (min 1 (ω k))

lemma scOffset_nonneg {n : ℕ} (ω : Fin n → ℝ) (k : Fin n) : 0 ≤ scOffset ω k :=
  le_max_left _ _

lemma scOffset_le_one {n : ℕ} (ω : Fin n → ℝ) (k : Fin n) : scOffset ω k ≤ 1 := by
  unfold scOffset; exact max_le (by norm_num) (min_le_left _ _)

/-- The "cut" event `Qset`: the offset of cluster `i` lies in the critical window. -/
def scQset {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (gam : ℝ) (i : Fin n) :
    Set (Fin n → ℝ) :=
  {ω | scThreshold clusters (scOffset ω) Δ β z i ≤ scOffset ω i ∧
       scOffset ω i ≤ scThreshold clusters (scOffset ω) Δ β z i + 2 * gam}

/-- The "win" event `Fset`: cluster `i` wins (its offset exceeds the threshold). -/
def scFset {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (i : Fin n) :
    Set (Fin n → ℝ) :=
  {ω | scThreshold clusters (scOffset ω) Δ β z i < scOffset ω i}

/-! ## Measurability -/

lemma measurable_scThreshold {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (i : Fin n) :
    Measurable (fun ω : Fin n → ℝ => scThreshold clusters (scOffset ω) Δ β z i) := by
  unfold scThreshold;
  -- Each term in the supremum is measurable, so the supremum itself is measurable.
  have h_term_measurable : ∀ j, Measurable (fun ω : Fin n → ℝ => β / Δ * (sparseF (clusters j) (scOffset ω j) Δ β z - Metric.infDist z (clusters i)ᶜ)) := by
    intro j
    unfold sparseF
    simp [scOffset];
    fun_prop;
  simp +decide [ Finset.sup'_eq_csSup_image ];
  -- The supremum of a finite set of measurable functions is measurable.
  have h_sup_measurable : ∀ (s : Finset (Fin n)), Measurable (fun ω : Fin n → ℝ => sSup (insert 0 (Set.image (fun j => β / Δ * (sparseF (clusters j) (scOffset ω j) Δ β z - Metric.infDist z (clusters i)ᶜ)) s))) := by
    intro s
    induction' s using Finset.induction with j s hj ih;
    · simp +decide [ Set.image ];
    · convert ih.sup ( h_term_measurable j ) using 1;
      ext ω; simp +decide [ Set.image_insert_eq, Set.insert_comm ] ;
      rw [ @csSup_insert ];
      · exact max_comm _ _;
      · exact Set.Finite.bddAbove ( Set.toFinite _ );
      · exact ⟨ 0, Set.mem_insert _ _ ⟩;
  convert h_sup_measurable ( Finset.univ \ { i } ) using 1;
  simp +decide [ Finset.sdiff_singleton_eq_erase ]

lemma measurable_scOffset_coord {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → ℝ => scOffset ω i) := by
  exact Measurable.max measurable_const ( Measurable.min measurable_const ( measurable_pi_apply i ) )

lemma measurable_bestContainingCluster {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i) (v : X) :
    Measurable (fun ω : Fin n → ℝ =>
      bestContainingCluster clusters (scOffset ω) Δ β v (hcover v)) := by
  let containing := Finset.univ.filter (fun i : Fin n => v ∈ clusters i)
  have hne : containing.Nonempty := by
    obtain ⟨i, hi⟩ := hcover v
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let score := fun i : Fin n => fun ω : Fin n → ℝ =>
    sparseF (clusters i) (scOffset ω i) Δ β v
  have hscore : ∀ i, Measurable (score i) := by
    intro i
    unfold score sparseF
    exact (measurable_scOffset_coord i).mul_const (Δ / β) |>.add measurable_const
  let maxScore := containing.sup' hne score
  have hmax : Measurable maxScore := Finset.measurable_sup' hne fun i _ => hscore i
  refine measurable_to_countable' fun i => ?_
  have hresult : MeasurableSet {ω : Fin n → ℝ |
      (i ∈ containing ∧ score i ω = maxScore ω) ∧
        ∀ b : Fin n, (b ∈ containing ∧ score b ω = maxScore ω) → i ≤ b} := by
    exact (Measurable.and
      (Measurable.and measurable_const
        (MeasurableSet.mem (measurableSet_eq_fun (hscore i) hmax)))
      (Measurable.forall fun b =>
        Measurable.imp (Measurable.and measurable_const
          (MeasurableSet.mem (measurableSet_eq_fun (hscore b) hmax))) measurable_const)).setOf
  change MeasurableSet {ω : Fin n → ℝ |
    bestContainingCluster clusters (scOffset ω) Δ β v (hcover v) = i}
  simpa only [bestContainingCluster, containing, score, maxScore, Finset.min'_eq_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.sup'_apply]
    using hresult

lemma measurable_scPartition_label {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i) (v : X) :
    Measurable (fun ω : Fin n → ℝ =>
      (scPartition clusters (scOffset ω) Δ β hcover).label v) := by
  exact (show Measurable (fun i : Fin n => i.val) by measurability).comp
    (measurable_bestContainingCluster clusters Δ β hcover v)

lemma measurableSet_scQset {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (gam : ℝ) (i : Fin n) :
    MeasurableSet (scQset clusters Δ β z gam i) := by
  convert MeasurableSet.inter ?_ ?_ using 1;
  · exact measurableSet_le ( measurable_scThreshold clusters Δ β z i ) ( measurable_scOffset_coord i );
  · exact measurableSet_le ( measurable_scOffset_coord i ) ( Measurable.add ( measurable_scThreshold clusters Δ β z i ) measurable_const )

lemma measurableSet_scFset {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (i : Fin n) :
    MeasurableSet (scFset clusters Δ β z i) := by
  exact measurableSet_lt ( measurable_scThreshold clusters Δ β z i ) ( measurable_scOffset_coord i )

/-! ## The truncated-exponential one-coordinate (slice) bound -/

/-
The key conditional bound: the truncated-exponential measure of the critical window
`[ρ, ρ+2γ]` (after clamping into `[0,1]`) is at most `(1-α)` times the survival mass
beyond `ρ` plus the constant `1/(eˡ-1)`. Here `α = e^{-2γλ}`.
-/
lemma texp_slice_bound (l gam ρ : ℝ) (hl : 0 < l) (hgam0 : 0 ≤ gam) (hρ : 0 ≤ ρ) :
    texpMeasure l {y : ℝ | ρ ≤ max 0 (min 1 y) ∧ max 0 (min 1 y) ≤ ρ + 2 * gam}
      ≤ ENNReal.ofReal (1 - Real.exp (-2 * gam * l)) *
          (texpMeasure l {y : ℝ | ρ < max 0 (min 1 y)} +
            ENNReal.ofReal (1 / (Real.exp l - 1))) := by
  by_cases hρ1 : ρ > 1;
  · rw [ show { y : ℝ | ρ ≤ max 0 ( min 1 y ) ∧ max 0 ( min 1 y ) ≤ ρ + 2 * gam } = ∅ from _ ] <;> norm_num;
    exact Set.eq_empty_of_forall_notMem fun x hx => by cases hx.1 <;> linarith;
  · -- Apply the key fact that texpMeasure l is supported on Icc 0 1.
    have h_support : (texpMeasure l) {y | ρ ≤ max 0 (min 1 y) ∧ max 0 (min 1 y) ≤ ρ + 2 * gam} = (texpMeasure l) (Set.Icc ρ (min (ρ + 2 * gam) 1)) := by
      rw [ ← MeasureTheory.measure_congr ];
      rw [ MeasureTheory.ae_eq_set ];
      constructor <;> rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] <;> norm_num;
      · exact Filter.Eventually.of_forall fun x hx₁ hx₂ hx₃ => ⟨ Or.inr ⟨ by linarith, hx₁ ⟩, by linarith, fun hx₄ => by linarith ⟩;
      · filter_upwards [ show texpMeasure l ( Set.Icc 0 1 )ᶜ = 0 from by
                          unfold texpMeasure; aesop; ] with x hx;
        grind;
    have h_survival : (texpMeasure l) {y | ρ < max 0 (min 1 y)} = (texpMeasure l) (Set.Ioc ρ 1) := by
      have h_survival : {y | ρ < max 0 (min 1 y)} ∩ Set.Icc 0 1 = Set.Ioc ρ 1 := by
        ext y; simp [Set.mem_setOf_eq];
        grind;
      rw [ ← h_survival, texpMeasure ];
      rw [ MeasureTheory.withDensity_apply' ];
      rw [ MeasureTheory.withDensity_apply' ];
      rw [ MeasureTheory.Measure.restrict_restrict ];
      · rw [ MeasureTheory.Measure.restrict_restrict_of_subset ];
        exact Set.inter_subset_right;
      · exact measurableSet_lt measurable_const ( measurable_const.max ( measurable_const.min measurable_id' ) );
    have h_survival : (texpMeasure l) (Set.Ioc ρ 1) = ENNReal.ofReal (texpSurvivalFn l ρ) := by
      exact texpMeasure_Ioc hl hρ ( by linarith );
    have h_survival : (texpMeasure l) (Set.Icc ρ (min (ρ + 2 * gam) 1)) = ENNReal.ofReal ((Real.exp (-l * ρ) - Real.exp (-l * (min (ρ + 2 * gam) 1))) / (1 - Real.exp (-l))) := by
      apply texpMeasure_Icc_eq hl hρ (by
      exact le_min ( by linarith ) ( by linarith )) (by
      exact min_le_right _ _);
    have h_survival : (texpMeasure l) (Set.Ioc ρ 1) + ENNReal.ofReal (1 / (Real.exp l - 1)) = ENNReal.ofReal (Real.exp (-l * ρ) / (1 - Real.exp (-l))) := by
      rw [ ‹ ( texpMeasure l ) ( Ioc ρ 1 ) = ENNReal.ofReal ( texpSurvivalFn l ρ ) ›, ← ENNReal.ofReal_add ];
      · unfold texpSurvivalFn;
        rw [ show ( Real.exp l - 1 ) = ( 1 - Real.exp ( -l ) ) * Real.exp l by rw [ sub_mul, one_mul, ← Real.exp_add ] ; norm_num ] ; norm_num [ Real.exp_neg, Real.exp_ne_zero, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
      · exact div_nonneg ( sub_nonneg.2 <| Real.exp_le_exp.2 <| by nlinarith ) <| sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith;
      · exact div_nonneg zero_le_one ( sub_nonneg.2 <| Real.one_le_exp hl.le );
    rw [ h_support, ‹ ( texpMeasure l ) ( Icc ρ ( min ( ρ + 2 * gam ) 1 ) ) = _ ›, ‹ ( texpMeasure l ) { y | ρ < max 0 ( min 1 y ) } = _ ›, h_survival ];
    rw [ ← ENNReal.ofReal_mul ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by nlinarith ) ] ; ring_nf ;
    rw [ show - ( l * min ( ρ + gam * 2 ) 1 ) = - ( l * ρ ) + - ( l * ( min ( ρ + gam * 2 ) 1 - ρ ) ) by ring, Real.exp_add ] ; ring_nf ;
    exact ENNReal.ofReal_le_ofReal ( sub_le_sub_left ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases min_cases ( ρ + gam * 2 ) 1 <;> nlinarith ) <| mul_nonneg ( Real.exp_nonneg _ ) <| inv_nonneg.mpr <| sub_nonneg.mpr <| Real.exp_le_one_iff.mpr <| by linarith ) _ )

/-! ## The per-cluster cut probability bound (Fubini + slice) -/

lemma mu_scQset_le {X : Type*} [PseudoMetricSpace X] {n : ℕ} [NeZero n]
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X) (gam : ℝ) (hgam0 : 0 ≤ gam)
    (l : ℝ) (hl : 0 < l) (i : Fin n) :
    haveI : IsProbabilityMeasure (texpMeasure l) := texpMeasure_isProbabilityMeasure hl
    (Measure.pi (fun _ : Fin n => texpMeasure l)) (scQset clusters Δ β z gam i)
      ≤ ENNReal.ofReal (1 - Real.exp (-2 * gam * l)) *
          ((Measure.pi (fun _ : Fin n => texpMeasure l)) (scFset clusters Δ β z i)
            + ENNReal.ofReal (1 / (Real.exp l - 1))) := by
  convert pi_measure_slice_le ( texpMeasure l ) i ( scQset clusters Δ β z gam i ) ( scFset clusters Δ β z i ) _ _ _ _ _ using 1;
  · exact texpMeasure_sigmaFinite hl;
  · exact texpMeasure_isProbabilityMeasure hl;
  · exact measurableSet_scQset clusters Δ β z gam i;
  · exact measurableSet_scFset clusters Δ β z i;
  · intro rest
    set ρ := scThreshold clusters (scOffset (fun j => if h : j = i then 0 else rest ⟨j, h⟩)) Δ β z i
    have hρ_nonneg : 0 ≤ ρ := by
      exact scThreshold_nonneg clusters _ _ _ _ _
    have hρ_eq : ∀ y : ℝ, scThreshold clusters (scOffset (fun j => if h : j = i then y else rest ⟨j, h⟩)) Δ β z i = ρ := by
      intro y
      apply scThreshold_congr clusters (scOffset (fun j => if h : j = i then y else rest ⟨j, h⟩)) (scOffset (fun j => if h : j = i then 0 else rest ⟨j, h⟩)) Δ β z i
      intro j hj
      simp [scOffset, hj]
    simp [scQset, scFset, hρ_eq] at *;
    convert texp_slice_bound l gam ρ hl hgam0 hρ_nonneg using 1;
    · unfold scOffset; aesop;
    · simp +decide [ scOffset ]

/-! ## Disjointness of win events -/

lemma scFset_pairwiseDisjoint {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, z ∈ clusters i) :
    (C : Set (Fin n)).PairwiseDisjoint (fun i => scFset clusters Δ β z i) := by
  intro i hi j hj hij; simp_all +decide [ Set.disjoint_left ] ;
  intro ω hωi hωj; have := best_eq_of_gt_threshold clusters ( scOffset ω ) Δ β z i hΔ hβ ( hC i hi ) ( by simpa using hωi ) ( hcover z ) ; have := best_eq_of_gt_threshold clusters ( scOffset ω ) Δ β z j hΔ hβ ( hC j hj ) ( by simpa using hωj ) ( hcover z ) ; aesop;

/-! ## Core measure bound on the union of cut events -/

/-
The measure of the union of cut events over clusters containing `z` is at most
`(1 - e^{-2γl})` times the measure of the union of win events plus the constant `s/(eˡ-1)`.
-/
lemma mu_cut_le {X : Type*} [PseudoMetricSpace X] {n : ℕ} [NeZero n]
    (clusters : Fin n → Set X) (Δ β : ℝ) (s : ℕ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β)
    (hsparse : ∀ v : X, (Finset.univ.filter (fun i => v ∈ clusters i)).card ≤ s)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i)
    (gam : ℝ) (hgam0 : 0 ≤ gam) (l : ℝ) (hl : 0 < l) :
    haveI : IsProbabilityMeasure (texpMeasure l) := texpMeasure_isProbabilityMeasure hl
    (Measure.pi (fun _ : Fin n => texpMeasure l))
        (⋃ i ∈ Finset.univ.filter (fun i => z ∈ clusters i), scQset clusters Δ β z gam i)
      ≤ ENNReal.ofReal (1 - Real.exp (-2 * gam * l)) *
          ((Measure.pi (fun _ : Fin n => texpMeasure l))
              (⋃ i ∈ Finset.univ.filter (fun i => z ∈ clusters i), scFset clusters Δ β z i)
            + ENNReal.ofReal (s / (Real.exp l - 1))) := by
  refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
  rw [ MeasureTheory.measure_biUnion_finset ];
  · refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) _;
    use fun i => ENNReal.ofReal ( 1 - Real.exp ( -2 * gam * l ) ) * ( ( Measure.pi fun x => texpMeasure l ) ( scFset clusters Δ β z i ) + ENNReal.ofReal ( 1 / ( Real.exp l - 1 ) ) );
    · convert mu_scQset_le clusters Δ β z gam hgam0 l hl i using 1;
    · rw [ ← Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
      gcongr;
      simp +decide [ div_eq_mul_inv ];
      gcongr; exact mod_cast hsparse z;
  · convert scFset_pairwiseDisjoint clusters Δ β z hΔ hβ hcover ( Finset.univ.filter fun i => z ∈ clusters i ) ( fun i hi => Finset.mem_filter.mp hi |>.2 ) using 1;
  · exact fun b _ => measurableSet_scFset clusters Δ β z b

/-! ## Bad event is contained in the union of cut events -/

/-- If the ball `B(z, γΔ)` is **not** contained in the cluster of `z`, then some cluster
`i` containing `z` has its offset inside the critical window. This is the contrapositive of
the padding lemma, packaged as a set inclusion of the "bad" event into the union of cut
events `scQset` (with `gam = β·γ`). -/
lemma scBad_subset_cut {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (clusters : Fin n → Set X) (Δ β : ℝ) (z : X)
    (hΔ : 0 < Δ) (hβ : 0 < β)
    (hpad : ∀ v : X, ∃ k : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters k)
    (hcompl : ∀ k, (clusters k)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ k : Fin n, v ∈ clusters k)
    (γ : ℝ) (hγ0 : 0 ≤ γ) :
    {ω : Fin n → ℝ | ¬ (Metric.closedBall z (γ * Δ) ⊆
        (scPartition clusters (scOffset ω) Δ β hcover).cluster z)}
      ⊆ ⋃ i ∈ Finset.univ.filter (fun i => z ∈ clusters i),
          scQset clusters Δ β z (β * γ) i := by
  intro ω hω
  have hradius : β * γ * (Δ / β) = γ * Δ := by field_simp
  have hbad : ¬ (Metric.closedBall z (β * γ * (Δ / β)) ⊆
      (scPartition clusters (scOffset ω) Δ β hcover).cluster z) := by
    rwa [hradius]
  obtain ⟨i, hzi, h1, h2⟩ := bad_imp_mem_Qbar clusters (scOffset ω) Δ β z hΔ hβ
    (scOffset_nonneg ω) (scOffset_le_one ω) hpad hcompl hcover (β * γ)
    (mul_nonneg hβ.le hγ0) hbad
  exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩) ⟨h1, h2⟩

/-! ## Generic measure-theoretic conversion -/

/-- Generic packaging step: from a covering of the complement of the "good" event `G` by a
set `EQ` whose measure is controlled in terms of `EF`, and an abstract real inequality
`hfinal`, conclude the padding lower bound on `μ G`. This isolates the measure-theoretic
bookkeeping (finiteness, `toReal` conversions) from the probabilistic content. -/
lemma padding_prob_from_cut {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ]
    (G EQ EF : Set α) (A D c : ℝ)
    (hA0 : 0 ≤ A) (hD0 : 0 ≤ D)
    (hsub : Gᶜ ⊆ EQ)
    (hcut : μ EQ ≤ ENNReal.ofReal A * (μ EF + ENNReal.ofReal D))
    (hfinal : ∀ sum_F sum_Q : ℝ, sum_F ≤ 1 → 0 ≤ sum_Q →
        sum_Q ≤ A * (sum_F + D) → 1 - sum_Q ≥ c) :
    μ.toOuterMeasure G ≥ ENNReal.ofReal c := by
  rw [Measure.toOuterMeasure_apply]
  have hEFne : μ EF ≠ ⊤ := (measure_lt_top μ EF).ne
  have hbadle : μ Gᶜ ≤ μ EQ := measure_mono hsub
  have hcut' : μ Gᶜ ≤ ENNReal.ofReal A * (μ EF + ENNReal.ofReal D) := le_trans hbadle hcut
  have hRHSne : ENNReal.ofReal A * (μ EF + ENNReal.ofReal D) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.add_ne_top.2 ⟨hEFne, ENNReal.ofReal_ne_top⟩
  have hbadne : μ Gᶜ ≠ ⊤ := ne_top_of_le_ne_top hRHSne hcut'
  set sum_F := (μ EF).toReal with hsumF
  set sum_Q := (μ Gᶜ).toReal with hsumQ
  have hF1 : sum_F ≤ 1 := by
    rw [hsumF, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal hEFne (by simp)).2 prob_le_one
  have hQ0 : 0 ≤ sum_Q := ENNReal.toReal_nonneg
  have hQb : sum_Q ≤ A * (sum_F + D) := by
    have h := (ENNReal.toReal_le_toReal hbadne hRHSne).2 hcut'
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0,
      ENNReal.toReal_add hEFne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hD0] at h
    exact h
  have hc : 1 - sum_Q ≥ c := hfinal sum_F sum_Q hF1 hQ0 hQb
  have hsum1 : (1 : ENNReal) ≤ μ G + μ Gᶜ := by
    calc (1 : ENNReal) = μ Set.univ := (measure_univ).symm
    _ = μ (G ∪ Gᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ G + μ Gᶜ := measure_union_le _ _
  have hGne : μ G ≠ ⊤ := (measure_lt_top μ G).ne
  have hGreal : 1 - sum_Q ≤ (μ G).toReal := by
    have h := (ENNReal.toReal_le_toReal (by simp) (ENNReal.add_ne_top.2 ⟨hGne, hbadne⟩)).2 hsum1
    rw [ENNReal.toReal_one, ENNReal.toReal_add hGne hbadne] at h
    linarith
  have hcle : c ≤ (μ G).toReal := le_trans hc hGreal
  calc ENNReal.ofReal c ≤ ENNReal.ofReal ((μ G).toReal) := ENNReal.ofReal_le_ofReal hcle
  _ = μ G := ENNReal.ofReal_toReal hGne

/-! ## Main padding probability theorem -/

universe u

/-- The padding probability bound: with the random clamped-offset partition coming from a
sparse cover (with nonempty cluster complements), the ball `B(z, γΔ)` is contained in the
partition cluster of `z` with probability at least `e^{-4βλγ}`, where `λ = 2 + 2 ln s`. -/
theorem sc_padding_prob {X : Type u} [PseudoMetricSpace X] {n : ℕ} [NeZero n]
    (clusters : Fin n → Set X) (β : ℝ) (s : ℕ) (Δ : ℝ)
    (hβ : 0 < β) (hs : 1 ≤ s) (hΔ : 0 < Δ)
    (hpad : ∀ v : X, ∃ i : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters i)
    (hsparse : ∀ v : X, (Finset.univ.filter (fun i => v ∈ clusters i)).card ≤ s)
    (hcompl : ∀ i, (clusters i)ᶜ.Nonempty)
    (hcover : ∀ v : X, ∃ i : Fin n, v ∈ clusters i)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ ≤ 1 / (4 * β)) (z : X) :
    haveI : IsProbabilityMeasure (texpMeasure (2 + 2 * Real.log s)) :=
      texpMeasure_isProbabilityMeasure (by linarith [lambda_ge_two s hs])
    (Measure.pi (fun _ : Fin n => texpMeasure (2 + 2 * Real.log s))).toOuterMeasure
        {ω | Metric.closedBall z (γ * Δ) ⊆
          (scPartition clusters (scOffset ω) Δ β hcover).cluster z}
      ≥ ENNReal.ofReal (Real.exp (-(4 * β * (2 + 2 * Real.log s)) * γ)) := by
  have hl : 0 < 2 + 2 * Real.log s := by linarith [lambda_ge_two s hs]
  haveI : IsProbabilityMeasure (texpMeasure (2 + 2 * Real.log s)) :=
    texpMeasure_isProbabilityMeasure hl
  -- The constants entering the bound.
  set A : ℝ := 1 - Real.exp (-2 * (β * γ) * (2 + 2 * Real.log s)) with hA
  set D : ℝ := (s : ℝ) / (Real.exp (2 + 2 * Real.log s) - 1) with hD
  have hexp_le_one : Real.exp (-2 * (β * γ) * (2 + 2 * Real.log s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hβ.le hγ0])
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hexp_gt_one : 1 < Real.exp (2 + 2 * Real.log s) := Real.one_lt_exp_iff.mpr hl
  have hD0 : 0 ≤ D := by
    rw [hD]; exact div_nonneg (by positivity) (by linarith)
  -- Apply the generic packaging lemma.
  apply padding_prob_from_cut
    (Measure.pi (fun _ : Fin n => texpMeasure (2 + 2 * Real.log s)))
    {ω | Metric.closedBall z (γ * Δ) ⊆
        (scPartition clusters (scOffset ω) Δ β hcover).cluster z}
    (⋃ i ∈ Finset.univ.filter (fun i => z ∈ clusters i), scQset clusters Δ β z (β * γ) i)
    (⋃ i ∈ Finset.univ.filter (fun i => z ∈ clusters i), scFset clusters Δ β z i)
    A D (Real.exp (-(4 * β * (2 + 2 * Real.log s)) * γ)) hA0 hD0
  · -- The bad event is contained in the union of cut events.
    intro ω hω
    exact scBad_subset_cut clusters Δ β z hΔ hβ hpad hcompl hcover γ hγ0 hω
  · -- The cut bound from Fubini and the slice estimate.
    exact mu_cut_le clusters Δ β s z hΔ hβ hsparse hcover (β * γ) (mul_nonneg hβ.le hγ0)
      (2 + 2 * Real.log s) hl
  · -- The final algebraic conclusion.
    intro sum_F sum_Q hF hQ0 hQb
    have hbound : sum_Q ≤ (1 - Real.exp (-(2 * β * γ * (2 + 2 * Real.log s)))) *
        (sum_F + (s : ℝ) / (Real.exp (2 + 2 * Real.log s) - 1)) := by
      have heq : -(2 * β * γ * (2 + 2 * Real.log s)) = -2 * (β * γ) * (2 + 2 * Real.log s) := by
        ring
      rw [heq]
      have : sum_Q ≤ A * (sum_F + D) := hQb
      rw [hA, hD] at this
      exact this
    have hfin := padding_prob_bound_abstract β γ s hβ hγ0 hγδ hs sum_F hF sum_Q hbound
      (1 - sum_Q) rfl
    have heq2 : -(4 * β * (2 + 2 * Real.log s) * γ) = -(4 * β * (2 + 2 * Real.log s)) * γ := by ring
    rw [heq2] at hfin
    exact hfin

end
