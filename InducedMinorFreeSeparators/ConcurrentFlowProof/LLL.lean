import Mathlib

open MeasureTheory ProbabilityTheory Finset Set

noncomputable section

variable {Ω : Type*} {ι : Type*} [MeasurableSpace Ω]


/-- The **lopsidependence condition**: for each event `A i`, and any subset `S` of indices
outside the dependency neighborhood `Γ i` (and not equal to `i`), the event `A i` is
independent of the intersection of complements `⋂ j ∈ S, (A j)ᶜ`. -/
def LopsidependenceCondition
    [DecidableEq ι]
    (A : ι → Set Ω) (Γ : ι → Finset ι) (μ : Measure Ω) : Prop :=
  ∀ i : ι, ∀ S : Finset ι,
    (∀ j ∈ S, j ∉ Γ i ∧ j ≠ i) →
    μ (A i ∩ ⋂ j ∈ (S : Set ι), (A j)ᶜ) ≤ μ (A i) * μ (⋂ j ∈ (S : Set ι), (A j)ᶜ)

/-! ### avoidSet: intersection of complements -/

/-- `avoidSet A S` is the event that none of the "bad" events `A j` for `j ∈ S` occur. -/
def avoidSet (A : ι → Set Ω) (S : Finset ι) : Set Ω :=
  ⋂ j ∈ (S : Set ι), (A j)ᶜ

omit [MeasurableSpace Ω] in
@[simp]
lemma avoidSet_empty (A : ι → Set Ω) : avoidSet A ∅ = univ := by
  simp [avoidSet]

lemma avoidSet_measurable [DecidableEq ι] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (S : Finset ι) : MeasurableSet (avoidSet A S) :=
  MeasurableSet.biInter (Finset.countable_toSet S) (fun i _ => (hA i).compl)

omit [MeasurableSpace Ω] in
lemma avoidSet_insert [DecidableEq ι] (A : ι → Set Ω) (S : Finset ι) (i : ι) (_hi : i ∉ S) :
    avoidSet A (insert i S) = (A i)ᶜ ∩ avoidSet A S := by
  simp only [avoidSet, Finset.coe_insert, Set.biInter_insert]

omit [MeasurableSpace Ω] in
lemma avoidSet_mono [DecidableEq ι] (A : ι → Set Ω) {S T : Finset ι} (h : S ⊆ T) :
    avoidSet A T ⊆ avoidSet A S :=
  Set.biInter_subset_biInter_left (Finset.coe_subset.mpr h)

/-! ### Measure decomposition -/

/-- For `i ∈ S`, the set `avoidSet A (S.erase i)` decomposes as the disjoint union of
`avoidSet A S` and `A i ∩ avoidSet A (S.erase i)`. -/
lemma measure_avoidSet_erase [DecidableEq ι]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Finset ι} {i : ι} (_hi : i ∈ S) :
    μ (avoidSet A (S.erase i)) =
      μ (avoidSet A S) + μ (A i ∩ avoidSet A (S.erase i)) := by
  rw [ ← MeasureTheory.measure_union, Set.union_comm ];
  · congr with x ; simp +decide [ avoidSet ];
    grind;
  · rw [ Set.disjoint_left ];
    unfold avoidSet; aesop;
  · exact MeasurableSet.inter ( hA i ) ( avoidSet_measurable A hA _ )

/-- `μ(avoidSet A S) ≠ ⊤` in a probability space. -/
lemma avoidSet_ne_top [DecidableEq ι]
    {A : ι → Set Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Finset ι) : μ (avoidSet A S) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_ne_top μ _) (measure_mono (subset_univ _))

/-! ### The key inductive claim -/

/-- The combined inductive statement of the LLL:
1. For all `i ∉ S`, `μ(A i ∩ avoidSet A S).toReal ≤ x i * μ(avoidSet A S).toReal`
2. `∏ j ∈ S, (1 - x j) ≤ μ(avoidSet A S).toReal` -/
def LLL_Statement
    (A : ι → Set Ω) (μ : Measure Ω) (x : ι → ℝ) (S : Finset ι) : Prop :=
  (∀ i : ι, i ∉ S →
    (μ (A i ∩ avoidSet A S)).toReal ≤ x i * (μ (avoidSet A S)).toReal) ∧
  (∏ j ∈ S, (1 - x j) ≤ (μ (avoidSet A S)).toReal)

/-- Base case: the LLL statement holds for the empty set. -/
lemma lll_base_case
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (_hA : ∀ i, MeasurableSet (A i))
    {x : ι → ℝ}
    (hLLL : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ (∅ : Finset ι), (1 - x j)) :
    LLL_Statement A μ x ∅ := by
  constructor <;> intros <;> simp_all +decide

/-- **The peeling lemma**: Given that the key claim holds for all strict subsets of `S`,
the measure of `avoidSet A S` can be bounded from below by peeling off elements of
a subset `S₁ ⊆ S`. -/
lemma lll_peeling
    [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {x : ι → ℝ}
    (_hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    {S : Finset ι}
    (ih : ∀ T : Finset ι, T ⊂ S →
      ∀ j : ι, j ∉ T →
        (μ (A j ∩ avoidSet A T)).toReal ≤ x j * (μ (avoidSet A T)).toReal)
    {S₁ : Finset ι} (hS₁ : S₁ ⊆ S) :
    (μ (avoidSet A S)).toReal ≥
      (∏ j ∈ S₁, (1 - x j)) * (μ (avoidSet A (S \ S₁))).toReal := by
  induction' S₁ using Finset.induction with j S₁ ih hS₁;
  · simp +decide;
  · rename_i h;
    have ih_step : (μ (avoidSet A (S \ S₁))).toReal ≥ (1 - x j) * (μ (avoidSet A ((S \ S₁) \ {j}))).toReal := by
      have ih_step : (μ (A j ∩ avoidSet A ((S \ S₁) \ {j}))).toReal ≤ x j * (μ (avoidSet A ((S \ S₁) \ {j}))).toReal := by
        grind +extAll;
      have ih_step : (μ (avoidSet A ((S \ S₁) \ {j}))).toReal = (μ (avoidSet A (S \ S₁))).toReal + (μ (A j ∩ avoidSet A ((S \ S₁) \ {j}))).toReal := by
        rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
        · congr with ω ; simp +decide [ avoidSet ];
          grind;
        · simp +contextual [ Set.disjoint_left, avoidSet ];
          exact fun ω hω => hω j ( hS₁ ( Finset.mem_insert_self _ _ ) ) ih;
        · exact MeasurableSet.inter ( hA j ) ( avoidSet_measurable A hA _ );
        · exact MeasureTheory.measure_ne_top _ _;
        · exact MeasureTheory.measure_ne_top _ _;
      nlinarith [ hx_lt_one j ];
    simp_all +decide [ Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase ];
    nlinarith [ h ( Finset.Subset.trans ( Finset.subset_insert _ _ ) hS₁ ), hx_lt_one j, show 0 ≤ ∏ j ∈ S₁, ( 1 - x j ) from Finset.prod_nonneg fun i hi => sub_nonneg.2 ( le_of_lt ( hx_lt_one i ) ) ]

/-- The main inductive theorem: the combined LLL statement holds for all finite sets,
proved by strong induction using the peeling lemma. -/
theorem lll_inductive
    [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {Γ : ι → Finset ι}
    (_hΓ : ∀ i, i ∉ Γ i)
    (hIndep : LopsidependenceCondition A Γ μ)
    {x : ι → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hLLL : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (S : Finset ι) :
    LLL_Statement A μ x S := by
  induction' S using Finset.strongInduction with S ih;
  refine' ⟨ _, _ ⟩;
  · intro i hi
    have h_bound : (μ (A i ∩ avoidSet A S)).toReal ≤ (μ (A i)).toReal * (μ (avoidSet A (S.filter (fun j => j ∉ Γ i)))).toReal := by
      have h1 : (μ (A i ∩ avoidSet A S)).toReal ≤ (μ (A i ∩ avoidSet A (S.filter (fun j => j ∉ Γ i)))).toReal := by
        apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
        · exact MeasureTheory.measure_ne_top _ _;
        · simp +contextual [ Set.subset_def, avoidSet ];
      have h2 : μ (A i ∩ avoidSet A (S.filter (fun j => j ∉ Γ i))) ≤
          μ (A i) * μ (avoidSet A (S.filter (fun j => j ∉ Γ i))) := by
        have := hIndep i (S.filter fun j => j ∉ Γ i) (fun j hj => by aesop)
        convert this using 2
      have h3 : (μ (A i ∩ avoidSet A (S.filter (fun j => j ∉ Γ i)))).toReal ≤
          (μ (A i)).toReal * (μ (avoidSet A (S.filter (fun j => j ∉ Γ i)))).toReal := by
        rw [← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) h2
      linarith;
    have h_ind : (μ (avoidSet A S)).toReal ≥ (∏ j ∈ S.filter (fun j => j ∈ Γ i), (1 - x j)) * (μ (avoidSet A (S.filter (fun j => j ∉ Γ i)))).toReal := by
      convert lll_peeling hA hx_nonneg hx_lt_one _ _ using 1;
      any_goals exact S.filter fun j => j ∈ Γ i;
      · rcongr j ; aesop;
      · infer_instance;
      · exact fun T hT j hj => ih T hT |>.1 j hj;
      · exact Finset.filter_subset _ _;
    have h_prod : (∏ j ∈ Γ i, (1 - x j)) ≤ (∏ j ∈ S.filter (fun j => j ∈ Γ i), (1 - x j)) := by
      rw [ ← Finset.prod_sdiff ( show S.filter ( fun j => j ∈ Γ i ) ⊆ Γ i from fun j hj => by aesop ) ];
      exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 ( le_of_lt ( hx_lt_one _ ) ) ) ( Finset.prod_le_one ( fun _ _ => sub_nonneg.2 ( le_of_lt ( hx_lt_one _ ) ) ) fun _ _ => sub_le_self _ ( hx_nonneg _ ) );
    refine' le_trans h_bound ( le_trans ( mul_le_mul_of_nonneg_right ( hLLL i ) ( ENNReal.toReal_nonneg ) ) _ );
    rw [ mul_assoc ];
    exact mul_le_mul_of_nonneg_left ( le_trans ( mul_le_mul_of_nonneg_right h_prod ( ENNReal.toReal_nonneg ) ) h_ind ) ( hx_nonneg i );
  · have := @lll_peeling;
    specialize this hA hx_nonneg hx_lt_one ( fun T hT j hj => ih T hT |>.1 j hj ) ( Finset.Subset.refl S );
    simp_all +decide

/-! ### Main theorem statements -/

/-- **The Lovász Local Lemma (Asymmetric Version).**

Let `(Ω, μ)` be a probability space and `{A i}` a finite family of measurable events.
Let `Γ i` be a dependency neighborhood for each event (with `i ∉ Γ i`), satisfying the
lopsidependence condition. If there exist real numbers `x i ∈ [0, 1)` such that for
each `i`:

  `μ(A i).toReal ≤ x i · ∏ j ∈ Γ i, (1 - x j)`

then the probability that none of the events occur satisfies:

  `μ(⋂ i, (A i)ᶜ) ≥ ∏ i, (1 - x i) > 0` -/
theorem lovasz_local_lemma
    [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {Γ : ι → Finset ι}
    (hΓ : ∀ i, i ∉ Γ i)
    (hIndep : LopsidependenceCondition A Γ μ)
    {x : ι → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hLLL : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ENNReal.ofReal (∏ i : ι, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ) := by
  convert ENNReal.ofReal_le_iff_le_toReal _ |>.2 _;
  · exact MeasureTheory.measure_ne_top _ _;
  · convert lll_inductive hA hΓ hIndep hx_nonneg hx_lt_one hLLL Finset.univ |>.2;
    ext; simp [avoidSet]

/-- The probability that none of the events occur is positive under the asymmetric LLL
conditions. -/
theorem lovasz_local_lemma_pos
    [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {Γ : ι → Finset ι}
    (hΓ : ∀ i, i ∉ Γ i)
    (hIndep : LopsidependenceCondition A Γ μ)
    {x : ι → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hLLL : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  calc 0 < ENNReal.ofReal (∏ i : ι, (1 - x i)) := by
          apply ENNReal.ofReal_pos.mpr
          exact Finset.prod_pos (fun i _ => by linarith [hx_lt_one i])
       _ ≤ μ (⋂ i, (A i)ᶜ) := lovasz_local_lemma hA hΓ hIndep hx_nonneg hx_lt_one hLLL

/-- **The Lovász Local Lemma (Symmetric Version).**

If each event has probability at most `p`, each event has at most `d` neighbors in the
dependency graph, and `4 * p * (d + 1) ≤ 1`, then the probability of avoiding all events
is positive.

The condition `4p(d+1) ≤ 1` is a convenient sufficient condition, slightly weaker than
the optimal `ep(d+1) ≤ 1`. When `d = 0` (all events mutually independent), this
requires `p ≤ 1/4`.

The proof instantiates the asymmetric LLL with `x i = 1 / (2 * (d + 1))` for all `i`,
and uses Bernoulli's inequality to verify the LLL condition. -/
theorem lovasz_local_lemma_symmetric
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {Γ : ι → Finset ι}
    (hΓself : ∀ i, i ∉ Γ i)
    (hIndep : LopsidependenceCondition A Γ μ)
    {p : ℝ} (_hp : 0 ≤ p)
    {d : ℕ}
    (hprob : ∀ i, (μ (A i)).toReal ≤ p)
    (hdeg : ∀ i, (Γ i).card ≤ d)
    (hcond : 4 * p * (↑d + 1) ≤ 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  convert lovasz_local_lemma_pos hA hΓself hIndep _ _ _ using 1;
  use fun _ => 1 / ( 2 * ( d + 1 ) );
  · exact fun i => by positivity;
  · exact fun i => by rw [ div_lt_iff₀ ] <;> linarith;
  · intro i
    have h_bound : (∏ j ∈ Γ i, (1 - 1 / (2 * (d + 1) : ℝ))) ≥ 1 / 2 := by
      have h_bernoulli : (1 - 1 / (2 * (d + 1) : ℝ)) ^ d ≥ 1 - d / (2 * (d + 1) : ℝ) := by
        exact le_trans ( by ring_nf; norm_num ) ( one_add_mul_le_pow ( by linarith [ show ( 1 : ℝ ) / ( 2 * ( d + 1 ) ) ≤ 1 by rw [ div_le_iff₀ ] <;> linarith ] ) _ );
      simp +zetaDelta at *;
      exact le_trans ( by rw [ div_eq_mul_inv ] at *; nlinarith [ mul_inv_cancel₀ ( by linarith : ( d : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( 2 * ( d + 1 ) : ℝ ) ≠ 0 ) ] ) ( pow_le_pow_of_le_one ( sub_nonneg.2 <| by rw [ inv_mul_le_iff₀ ] <;> norm_num <;> linarith ) ( sub_le_self _ <| by positivity ) <| hdeg i );
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ hprob i, show ( d : ℝ ) + 1 ≥ 1 by linarith, one_div_mul_cancel ( by linarith : ( 2 * ( d + 1 ) : ℝ ) ≠ 0 ) ]

end
