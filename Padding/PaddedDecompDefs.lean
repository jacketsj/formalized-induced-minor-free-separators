/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.PaddedDecompDef

/-! # Padded Decompositions — Auxiliary Lemmas and Proof-Side Definitions

The definitions needed to **state** the padded-decomposition results live in
`Padding/Statements/PaddedDecompDef.lean`.  This file collects the auxiliary
lemmas about those notions, together with definitions (such as `HasPaddedModulus`) that are
used only inside the proofs.  None of the contents of this file are needed to read the
statements of the headline theorems; it is imported only by the implementation files.

## Contents

* Basic API lemmas for `Partition`, `Partition.cluster`, and `Partition.IsBounded`.
* Monotonicity lemmas for `PaddedDecomp` / `AdmitsPaddedDecompScheme` in `β` and `δ`.
* `PaddedDecomposition.HasPaddedModulus`: a deterministic padded-modulus notion used in the
  proof of the average-distortion embedding theorem.
-/

open MeasureTheory Metric Set Real

namespace PaddedDecomposition

noncomputable section

namespace Partition

variable {X : Type*}

instance : Inhabited (Partition X) := ⟨⟨fun _ => 0⟩⟩

@[simp]
lemma coe_mk (f : X → ℕ) (x : X) : (⟨f⟩ : Partition X) x = f x := rfl

@[simp]
lemma mem_cluster_iff (P : Partition X) (w z : X) :
    w ∈ P.cluster z ↔ P w = P z :=
  Iff.rfl

lemma mem_cluster_self (P : Partition X) (z : X) : z ∈ P.cluster z := rfl

lemma cluster_symm (P : Partition X) (x z : X) :
    x ∈ P.cluster z ↔ z ∈ P.cluster x := by
  simp [cluster]; exact ⟨Eq.symm, Eq.symm⟩

lemma cluster_eq_of_mem (P : Partition X) {x z : X} (h : x ∈ P.cluster z) :
    P.cluster x = P.cluster z := by
  ext w; simp only [mem_cluster_iff]
  exact ⟨fun hw => hw.trans h, fun hw => hw.trans h.symm⟩

lemma cluster_eq_iff (P : Partition X) (x z : X) :
    P.cluster x = P.cluster z ↔ P x = P z :=
  ⟨fun h => by have := h ▸ mem_cluster_self P x; exact this,
   fun h => by ext w; simp [cluster, h]⟩

lemma cluster_eq_fiber (P : Partition X) (z : X) :
    P.cluster z = P.label ⁻¹' {P z} := by
  ext w; simp [cluster]

/-! ## Bounded partitions -/

lemma IsBounded.diam_le [PseudoMetricSpace X] {P : Partition X} {Δ : ℝ}
    (h : P.IsBounded Δ) (hΔ : 0 ≤ Δ) (z : X) : Metric.diam (P.cluster z) ≤ Δ := by
  convert ENNReal.toReal_le_of_le_ofReal _ _;
  · exact hΔ;
  · exact h z

lemma IsBounded.mono [PseudoMetricSpace X] {P : Partition X} {Δ₁ Δ₂ : ℝ}
    (h : P.IsBounded Δ₁) (hle : Δ₁ ≤ Δ₂) : P.IsBounded Δ₂ :=
  fun z => le_trans (h z) (ENNReal.ofReal_le_ofReal hle)

/-- If a partition is `Δ`-bounded, every cluster is contained in the closed ball
of radius `Δ` centered at any point in the cluster. -/
lemma IsBounded.cluster_subset_closedBall [PseudoMetricSpace X] {P : Partition X} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : P.IsBounded Δ) (z : X) :
    P.cluster z ⊆ Metric.closedBall z Δ := by
  intro w hw
  have h_dist : dist w z ≤ Metric.diam (P.cluster z) := by
    apply_rules [dist_le_diam_of_mem]
    exact Metric.isBounded_iff_ediam_ne_top.mpr (ne_of_lt (lt_of_le_of_lt (h z) ENNReal.ofReal_lt_top))
  exact le_trans h_dist (h.diam_le hΔ z)

lemma isBounded_of_diam_le [PseudoMetricSpace X] {P : Partition X} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : ∀ z : X, Bornology.IsBounded (P.cluster z))
    (hd : ∀ z : X, Metric.diam (P.cluster z) ≤ Δ) : P.IsBounded Δ := by
  convert hd using 1
  constructor <;> intro h <;> simp_all +decide [PaddedDecomposition.Partition.IsBounded, Metric.ediam]
  intro z i hi j hj
  exact le_trans (Metric.dist_le_diam_of_mem (by solve_by_elim) (by aesop) (by aesop)) (h z)

/-- The trivial partition placing all points in the same cluster. -/
def trivial : Partition X := ⟨fun _ => 0⟩

@[simp]
lemma trivial_apply (x : X) : (trivial : Partition X) x = 0 := rfl

@[simp]
lemma trivial_cluster (z : X) : (trivial : Partition X).cluster z = Set.univ := by
  ext w; simp [cluster, trivial]

end Partition

/-! ## Monotonicity properties -/

universe u

/-- A padded decomposition with parameter `β` is also a padded decomposition with any
larger `β'`. (A larger `β` gives a weaker padding guarantee.) -/
def PaddedDecomp.weaken_beta {X : Type u} [PseudoMetricSpace X] {β β' δ Δ : ℝ}
    (pd : PaddedDecomp X β δ Δ) (hle : β ≤ β') (_hδ : 0 ≤ δ) :
    PaddedDecomp X β' δ Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := pd.partition
  bounded := pd.bounded
  padding := fun γ hγ0 hγδ z => le_trans
    (by apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp_of_le; nlinarith)
    (pd.padding γ hγ0 hγδ z)

/-- A padded decomposition with parameter `δ` is also a padded decomposition with any
smaller `δ'`. (A smaller `δ` gives a weaker padding guarantee.) -/
def PaddedDecomp.weaken_delta {X : Type u} [PseudoMetricSpace X] {β δ δ' Δ : ℝ}
    (pd : PaddedDecomp X β δ Δ) (hle : δ' ≤ δ) :
    PaddedDecomp X β δ' Δ where
  Ω := pd.Ω
  msΩ := pd.msΩ
  μ := pd.μ
  hμ := pd.hμ
  partition := pd.partition
  bounded := pd.bounded
  padding := fun γ hγ0 hγδ z => pd.padding γ hγ0 (le_trans hγδ hle) z

lemma AdmitsPaddedDecompScheme.weaken {X : Type u} [PseudoMetricSpace X]
    {β β' δ δ' : ℝ} (h : AdmitsPaddedDecompScheme X β δ) (hβ : β ≤ β')
    (hδ : δ' ≤ δ) (hδ0 : 0 ≤ δ) :
    AdmitsPaddedDecompScheme X β' δ' :=
  fun Δ hΔ => (h Δ hΔ).map (fun pd => (pd.weaken_beta hβ hδ0).weaken_delta hδ)

/-! ## Padded Modulus -/

open Classical

/-- A finite metric space has **padded modulus** at most `α` if for every `Δ > 0`, there
exists a `Δ`-bounded partition where at least half of the points `z` have their ball
`B(z, Δ/α)` entirely contained in their cluster.

This deterministic notion is used in the proof of the average-distortion embedding theorem. -/
def HasPaddedModulus (X : Type*) [PseudoMetricSpace X] [Fintype X] (α : ℝ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → ∃ (P : Partition X), P.IsBounded Δ ∧
    2 * (Finset.univ.filter (fun z => Metric.closedBall z (Δ / α) ⊆ P.cluster z)).card ≥
      Fintype.card X

/-- HasPaddedModulus is monotone: a larger α gives a weaker condition. -/
lemma HasPaddedModulus.mono (X : Type*) [MetricSpace X] [Fintype X]
    {α α' : ℝ} (hα : 0 < α) (hle : α ≤ α') (h : HasPaddedModulus X α) :
    HasPaddedModulus X α' := by
  intro Δ hΔ
  obtain ⟨P, hP_bdd, hP_pad⟩ := h Δ hΔ
  refine ⟨P, hP_bdd, le_trans hP_pad (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  exact fun w hw => hz (Metric.closedBall_subset_closedBall
    (div_le_div_of_nonneg_left hΔ.le hα hle) hw)

end

end PaddedDecomposition
