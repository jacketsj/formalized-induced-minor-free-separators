/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.SparseCover
import Padding.PaddedDecompDefs
import Padding.SparseCover.PaddingProof
import Padding.SparseCover.TruncatedExponential
import Padding.SparseCover.PaddingMeasure
import Mathlib

/-! # From Sparse Covers to Padded Decompositions

This file packages the measure-theoretic core of the construction — the padding
probability bound `sc_padding_prob` proved in `Padding.SparseCover.PaddingMeasure` —
into the `PaddedDecomp` structure.

The random partition, the score function `sparseF`, the partition construction
`scPartition`, its boundedness, and the padding probability bound are all developed
*separately* in `PaddingMeasure.lean`; here we only assemble the final object.

## Main results

* `sparse_cover_to_padded_decomp`: A `(β, s, Δ)`-sparse cover with bounded clusters yields a
  `(4β·(2 + 2 ln s), 1/(4β), Δ)`-padded decomposition.
* `sparse_cover_scheme_to_padded_decomp_scheme`: the corresponding scheme-level statement.
-/

open MeasureTheory Metric Set Real PaddedDecomposition Classical

noncomputable section

universe u

/-- **Sparse Cover to Padded Decomposition** (Conroy–Filtser).

If a metric space `X` has a `(β, s, Δ)`-sparse cover with bounded clusters,
then it admits a `(4β·(2 + 2 ln s), 1/(4β), Δ)`-padded decomposition.

The probabilistic core (the padding probability bound) is `sc_padding_prob`; the
construction of the random partition (`scPartition`, `scOffset`) and the diameter bound
(`scPartition_bounded`) live in `Padding.SparseCover.PaddingMeasure`.

The proof reindexes the cover's clusters by `Fin n` (`n = |ι|`), uses the product of
`[0,1]`-truncated exponential measures as the sample space (transported to the universe of
`X` via `ULift`), and applies `sc_padding_prob`. Two degenerate cases are handled
separately: when `X` is empty, and when some cluster is the whole space (in which case the
trivial partition already works). -/
theorem sparse_cover_to_padded_decomp
    (X : Type u) [PseudoMetricSpace X] [Fintype X]
    (β : ℝ) (s : ℕ) (Δ : ℝ) (hβ : 0 < β) (hs : 1 ≤ s) (hΔ : 0 < Δ)
    (cover : SparseCover X β s Δ)
    (hbdd : ∀ i, Bornology.IsBounded (cover.cluster i)) :
    Nonempty (PaddedDecomp X (4 * β * (2 + 2 * Real.log s)) (1 / (4 * β)) Δ) := by
  set n := Fintype.card cover.ι with hn_def
  set e := Fintype.equivFin cover.ι with e_def
  set clusters := fun i : Fin n => cover.cluster (e.symm i) with clusters_def
  -- Each point lies in some cluster.
  have hcontain : ∀ v : X, ∃ i : Fin n, v ∈ clusters i := by
    intro v
    obtain ⟨j, hj⟩ := cover.padding v
    exact ⟨e j, by
      simp only [clusters_def, Equiv.symm_apply_apply]
      exact hj (mem_closedBall_self (div_nonneg hΔ.le hβ.le))⟩
  -- The padding property of the cover, reindexed.
  have hpad : ∀ v : X, ∃ i : Fin n, Metric.closedBall v (Δ / β) ⊆ clusters i := by
    intro v
    obtain ⟨j, hj⟩ := cover.padding v
    exact ⟨e j, by simpa only [clusters_def, Equiv.symm_apply_apply] using hj⟩
  -- The diameter bound of the cover, reindexed (as an `ediam` bound).
  have hediam : ∀ i : Fin n, Metric.ediam (clusters i) ≤ ENNReal.ofReal Δ := by
    intro i
    exact ediam_le_of_diam_le_of_bounded (cover.diam_le (e.symm i)) (hbdd (e.symm i))
  -- The sparsity property of the cover, reindexed.
  have hsparse : ∀ v : X,
      (Finset.univ.filter (fun i : Fin n => v ∈ clusters i)).card ≤ s := by
    intro v
    have hcard : (Finset.univ.filter (fun j : cover.ι => v ∈ cover.cluster j)).card
        = (Finset.univ.filter (fun i : Fin n => v ∈ clusters i)).card := by
      apply Finset.card_bij' (fun a _ => e a) (fun b _ => e.symm b)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        simp only [clusters_def, Equiv.symm_apply_apply]
        exact ha
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        simp only [clusters_def] at hb
        exact hb
      · intro a _; simp
      · intro b _; simp
    rw [← hcard]; exact cover.sparse v
  by_cases hn0 : n = 0
  · -- Degenerate case: `n = 0` forces `X` to be empty.
    have hXempty : IsEmpty X := by
      rw [← not_nonempty_iff]; rintro ⟨v⟩
      exact absurd (hcontain v).choose.isLt (by omega)
    exact ⟨⟨ULift.{u} Unit, ⊤, Measure.dirac ⟨()⟩, Measure.dirac.isProbabilityMeasure,
      fun _ => Partition.trivial, fun _ z => hXempty.elim z,
      fun _ _ => MeasurableSet.of_discrete, fun γ _ _ z => hXempty.elim z⟩⟩
  · haveI : NeZero n := ⟨hn0⟩
    by_cases hcompl : ∀ i : Fin n, (clusters i)ᶜ.Nonempty
    · -- Main case: all cluster complements are nonempty, apply `sc_padding_prob`.
      have hl : 0 < 2 + 2 * Real.log (↑s : ℝ) := by linarith [lambda_ge_two s hs]
      haveI : IsProbabilityMeasure (texpMeasure (2 + 2 * Real.log (↑s : ℝ))) :=
        texpMeasure_isProbabilityMeasure hl
      set baseμ : Measure (Fin n → ℝ) :=
        Measure.pi (fun _ : Fin n => texpMeasure (2 + 2 * Real.log (↑s : ℝ))) with baseμ_def
      haveI : IsProbabilityMeasure baseμ := by rw [baseμ_def]; infer_instance
      set dn := MeasurableEquiv.ulift (α := Fin n → ℝ) with dn_def
      haveI : IsProbabilityMeasure (baseμ.comap dn) := by
        constructor
        rw [MeasurableEmbedding.comap_apply dn.measurableEmbedding]; simp
      refine ⟨⟨ULift.{u} (Fin n → ℝ), inferInstance, baseμ.comap dn, inferInstance,
        fun ω => scPartition clusters (scOffset ω.down) Δ β hcontain,
        fun ω => scPartition_bounded clusters (scOffset ω.down) Δ β hediam hcontain,
        fun S z => by
          simp only [Set.subset_def, Partition.mem_cluster_iff]
          exact (Measurable.forall fun x => Measurable.imp measurable_const
            (MeasurableSet.mem (measurableSet_eq_fun
              ((measurable_scPartition_label clusters Δ β hcontain x).comp dn.measurable)
              ((measurable_scPartition_label clusters Δ β hcontain z).comp dn.measurable)))).setOf,
        fun γ hγ0 hγδ z => ?_⟩⟩
      rw [Measure.toOuterMeasure_apply, MeasurableEmbedding.comap_apply dn.measurableEmbedding]
      have himg : (⇑dn) ''
          {ω : ULift.{u} (Fin n → ℝ) | Metric.closedBall z (γ * Δ) ⊆
            (scPartition clusters (scOffset ω.down) Δ β hcontain).cluster z}
          = {g : Fin n → ℝ | Metric.closedBall z (γ * Δ) ⊆
            (scPartition clusters (scOffset g) Δ β hcontain).cluster z} := by
        ext g
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨ω, hω, rfl⟩; exact hω
        · intro hg; exact ⟨ULift.up g, hg, rfl⟩
      rw [himg]
      have hsc := sc_padding_prob clusters β s Δ hβ hs hΔ hpad hsparse hcompl hcontain
        γ hγ0 hγδ z
      rw [Measure.toOuterMeasure_apply] at hsc
      exact hsc
    · -- Degenerate case: some cluster is the whole space, so the trivial partition works.
      rw [not_forall] at hcompl
      obtain ⟨i, hi⟩ := hcompl
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hi
      have huniv : Metric.ediam (Set.univ : Set X) ≤ ENNReal.ofReal Δ := by
        rw [← hi]; exact hediam i
      refine ⟨⟨ULift.{u} Unit, ⊤, Measure.dirac ⟨()⟩, Measure.dirac.isProbabilityMeasure,
        fun _ => Partition.trivial, ?_, fun _ _ => MeasurableSet.of_discrete, ?_⟩⟩
      · intro _ z
        rw [Partition.trivial_cluster]; exact huniv
      · intro γ hγ0 hγδ z
        have hexp1 : Real.exp (-(4 * β * (2 + 2 * Real.log s)) * γ) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have h2 : 0 ≤ 2 + 2 * Real.log (↑s : ℝ) := by linarith [lambda_ge_two s hs]
          nlinarith [mul_nonneg (mul_nonneg hβ.le h2) hγ0]
        rw [ge_iff_le, Measure.toOuterMeasure_apply]
        refine le_trans (ENNReal.ofReal_le_one.mpr hexp1) ?_
        rw [← measure_univ (μ := Measure.dirac (⟨()⟩ : ULift.{u} Unit))]
        apply measure_mono
        intro ω _
        simp only [Set.mem_setOf_eq, Partition.trivial_cluster, Set.subset_univ]

/-- **Corollary**: A `(β, s)`-sparse cover scheme with bounded clusters implies a
padded decomposition scheme. -/
theorem sparse_cover_scheme_to_padded_decomp_scheme
    (X : Type u) [PseudoMetricSpace X] [Fintype X]
    (β : ℝ) (s : ℕ) (hβ : 0 < β) (hs : 1 ≤ s)
    (h : AdmitsSparseCoverScheme X β s)
    (hbdd : ∀ Δ > 0, ∀ cover : SparseCover X β s Δ,
      ∀ i, Bornology.IsBounded (cover.cluster i)) :
    PaddedDecomposition.AdmitsPaddedDecompScheme X
      (4 * β * (2 + 2 * Real.log s)) (1 / (4 * β)) := by
  intro Δ hΔ
  obtain ⟨cover⟩ := h Δ hΔ
  exact sparse_cover_to_padded_decomp X β s Δ hβ hs hΔ cover (hbdd Δ hΔ cover)

end
