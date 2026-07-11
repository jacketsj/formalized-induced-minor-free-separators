import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProductIndep

/-!
# LLL Proof for the Concurrent Flow Setting

This file provides the Lovász Local Lemma (LLL) infrastructure and
helper lemmas for the concurrent flow setting.
-/

open Finset SimpleGraph Real MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

/-! ## Product LLL infrastructure -/

section ProductLLL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]

lemma sum_prod_weight (g : ∀ i, β i → ℝ≥0∞) :
    ∑ f : ∀ i, β i, ∏ i, g i (f i) = ∏ i, ∑ b, g i b :=
  (Fintype.prod_sum g).symm

lemma total_weight_one (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1) :
    ∑ f : ∀ i, β i, ∏ i, g i (f i) = 1 := by
  rw [sum_prod_weight]; exact Finset.prod_eq_one fun i _ => hg i

lemma total_weight_ne_zero (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1) :
    ∑ f : ∀ i, β i, ∏ i, g i (f i) ≠ 0 := by
  rw [total_weight_one g hg]; exact one_ne_zero

lemma total_weight_ne_top (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1) :
    ∑ f : ∀ i, β i, ∏ i, g i (f i) ≠ ⊤ := by
  rw [total_weight_one g hg]; exact ENNReal.one_ne_top

lemma prod_measure_eq (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    (S : Set (∀ i, β i)) [∀ f, Decidable (f ∈ S)] :
    letI : MeasurableSpace (∀ i, β i) := ⊤
    (weightedPMF (fun f => ∏ i, g i (f i))
      (total_weight_ne_zero g hg) (total_weight_ne_top g hg)).toMeasure S =
    ∑ f : ∀ i, β i, if f ∈ S then ∏ i, g i (f i) else 0 := by
  unfold weightedPMF;
  simp +decide [ Set.indicator, total_weight_one g hg ]

lemma product_lopsidependence
    (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Set (∀ i, β i))
    (dep : κ → Finset ι)
    (hA_dep : ∀ k, ∀ f₁ f₂ : ∀ i, β i,
      (∀ i ∈ dep k, f₁ i = f₂ i) → (f₁ ∈ A k ↔ f₂ ∈ A k))
    (Γ : κ → Finset κ) (_hΓself : ∀ k, k ∉ Γ k)
    (hΓ_disjoint : ∀ k₁ k₂, k₂ ∉ Γ k₁ → k₂ ≠ k₁ →
      Disjoint (dep k₁) (dep k₂)) :
    letI : MeasurableSpace (∀ i, β i) := ⊤
    LopsidependenceCondition A Γ
      (weightedPMF (fun f => ∏ i, g i (f i))
        (total_weight_ne_zero g hg) (total_weight_ne_top g hg)).toMeasure := by
  intro k S hS
  let C := ⋂ j ∈ (S : Set κ), (A j)ᶜ
  let SgetParam := dep k
  let Tgetattr := Finset.biUnion S dep
  have hC_dep : ∀ f₁ f₂ : ∀ i, β i, (∀ i ∈ Tgetattr, f₁ i = f₂ i) → (f₁ ∈ C ↔ f₂ ∈ C) := by
    simp +zetaDelta at *; grind +qlia
  generalize_proofs at *;
  convert product_independence_thm g hg ( A k ) C SgetParam Tgetattr _ _ hC_dep |> le_of_eq using 1;
  · convert prod_measure_eq g hg ( A k ∩ C ) using 1;
  · convert congr_arg₂ ( · * · ) ( prod_measure_eq g hg ( A k ) ) ( prod_measure_eq g hg ( ⋂ j ∈ ( S : Set κ ), ( A j ) ᶜ ) ) using 1;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ j, hj₁, hj₂ ⟩ := Finset.mem_biUnion.mp hx₂; exact Finset.disjoint_left.mp ( hΓ_disjoint k j ( hS j hj₁ |>.1 ) ( hS j hj₁ |>.2 ) ) hx₁ hj₂;
  · exact hA_dep k

theorem product_lll
    (g : ∀ i, β i → ℝ≥0∞) (hg : ∀ i, ∑ b, g i b = 1)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Set (∀ i, β i))
    (dep : κ → Finset ι)
    (hA_dep : ∀ k, ∀ f₁ f₂ : ∀ i, β i,
      (∀ i ∈ dep k, f₁ i = f₂ i) → (f₁ ∈ A k ↔ f₂ ∈ A k))
    (Γ : κ → Finset κ) (hΓself : ∀ k, k ∉ Γ k)
    (hΓ_disjoint : ∀ k₁ k₂, k₂ ∉ Γ k₁ → k₂ ≠ k₁ →
      Disjoint (dep k₁) (dep k₂))
    (x : κ → ℝ)
    (hx_nonneg : ∀ k, 0 ≤ x k) (hx_lt_one : ∀ k, x k < 1)
    [∀ k f, Decidable (f ∈ A k)]
    (hprob : ∀ k,
      (∑ f : ∀ i, β i, if f ∈ A k then ∏ i, g i (f i) else 0).toReal ≤
      x k * ∏ j ∈ Γ k, (1 - x j)) :
    ∃ f : ∀ i, β i, (∀ i, 0 < g i (f i)) ∧ ∀ k, f ∉ A k := by
  have := @combinatorial_lll_asymmetric;
  convert this ( fun f => ∏ i, g i ( f i ) ) ( total_weight_ne_zero g hg ) ( total_weight_ne_top g hg ) A Γ hΓself x hx_nonneg hx_lt_one _ _ using 1;
  · ext f; simp [];
  · intro k; specialize hprob k; rw [ prod_measure_eq ] ; assumption; exact hg;
  · exact product_lopsidependence g hg A dep hA_dep Γ hΓself hΓ_disjoint

end ProductLLL

/-! ## Helper lemmas for Concurrent Flow -/

namespace SimpleGraph.LLLProof

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

omit [Nonempty V] [DecidableRel G.Adj] in
lemma exists_path_st (cf : ConcurrentFlow G) (s t : V) (hst : s ≠ t) :
    ∃ l ∈ cf.support, l.head? = some s ∧ l.getLast? = some t ∧ 0 < cf.flow l := by
  have := cf.total_flow s t hst;
  contrapose! this;
  rw [ Finset.sum_eq_zero ] <;> aesop

omit [Nonempty V] [DecidableRel G.Adj] in
lemma path_endpoints_ne (cf : ConcurrentFlow G) {l : List V} (hl : l ∈ cf.support) :
    ∀ s : V, ¬(l.head? = some s ∧ l.getLast? = some s) := by
  rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
  · exact absurd ( cf.valid _ hl ) ( by simp +decide );
  · have := cf.valid _ hl; simp_all +decide [ List.isChain_cons_cons ] ; grind

end SimpleGraph.LLLProof
end
