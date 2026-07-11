import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLL

open MeasureTheory Finset Set
open scoped BigOperators NNReal ENNReal

noncomputable section

def weightedPMF {α : Type*} [Fintype α] (f : α → ℝ≥0∞)
    (hf_ne_zero : Finset.sum Finset.univ f ≠ 0)
    (hf_ne_top : Finset.sum Finset.univ f ≠ ⊤) : PMF α :=
  PMF.normalize f (by rwa [tsum_fintype]) (by rwa [tsum_fintype])

theorem combinatorial_lll
    {α : Type*} [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : α → ℝ≥0∞)
    (hW : Finset.sum Finset.univ w ≠ 0)
    (hWtop : Finset.sum Finset.univ w ≠ ⊤)
    (B : ι → Set α)
    (Γ : ι → Finset ι)
    (hΓself : ∀ i, i ∉ Γ i)
    {p : ℝ} (hp : 0 ≤ p)
    {d : ℕ}
    (hprob : ∀ i,
      letI : MeasurableSpace α := ⊤
      ((weightedPMF w hW hWtop).toMeasure (B i)).toReal ≤ p)
    (hdeg : ∀ i, (Γ i).card ≤ d)
    (hcond : 4 * p * (↑d + 1) ≤ 1)
    (hIndep :
      letI : MeasurableSpace α := ⊤
      LopsidependenceCondition B Γ (weightedPMF w hW hWtop).toMeasure) :
    ∃ a : α, 0 < w a ∧ ∀ i, a ∉ B i := by
  letI : MeasurableSpace α := ⊤
  have hprob_meas : IsProbabilityMeasure (weightedPMF w hW hWtop).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hA_meas : ∀ i, MeasurableSet (B i) := fun _ => trivial
  have h_pos := lovasz_local_lemma_symmetric hA_meas hΓself hIndep hp hprob hdeg hcond
  contrapose! h_pos; simp_all [weightedPMF]
  intro a ha; specialize h_pos a; simp_all

theorem combinatorial_lll_asymmetric
    {α : Type*} [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : α → ℝ≥0∞)
    (hW : Finset.sum Finset.univ w ≠ 0)
    (hWtop : Finset.sum Finset.univ w ≠ ⊤)
    (B : ι → Set α)
    (Γ : ι → Finset ι)
    (hΓself : ∀ i, i ∉ Γ i)
    (x : ι → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hprob : ∀ i,
      letI : MeasurableSpace α := ⊤
      ((weightedPMF w hW hWtop).toMeasure (B i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (hIndep :
      letI : MeasurableSpace α := ⊤
      LopsidependenceCondition B Γ (weightedPMF w hW hWtop).toMeasure) :
    ∃ a : α, 0 < w a ∧ ∀ i, a ∉ B i := by
  letI : MeasurableSpace α := ⊤
  have hprob_meas : IsProbabilityMeasure (weightedPMF w hW hWtop).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hA_meas : ∀ i, MeasurableSet (B i) := fun _ => trivial
  have h_pos := lovasz_local_lemma_pos hA_meas hΓself hIndep hx_nonneg hx_lt_one hprob
  contrapose! h_pos; simp_all [weightedPMF]
  intro a ha; specialize h_pos a; simp_all

end
