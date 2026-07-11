/-
# Balanced Separators from Q̄ Bounds

This file proves the main results connecting Q̄ bounds to balanced separators.

## Main Results

* `threshold_no_edge` - edges can't cross the threshold slab
* `integral_slab_size` - integral identity for threshold slab sizes
* `integral_product_sizes` - integral identity for cut products
* `expansion_to_sep` - vertex expansion bounds yield balanced separators
* `sp_to_embed_feasibility` - feasible Q̄ solutions are bounded by Q̄
* `embed_to_sep` - Q̄ bounds for induced subgraphs yield balanced separators
* `Qbar_bound_gives_separator` - the main "putting it all together" result

## References

Sections "Preliminaries" and "Vertex Expansion, Metric Spread, Balanced
Separators, and Relaxations" of the paper.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.Peeling

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Threshold Rounding -/

omit [DecidableEq V] in
/-- For a Q̄-feasible pair `(ω, f)` and threshold `θ`, if `u` is below and `v`
is above the "slab" `{v : |f(v) - θ| ≤ ω(v)}`, then `u` and `v` are not
adjacent. This is the core separation property of threshold rounding. -/
theorem threshold_no_edge (G : SimpleGraph V)
    {ω f : V → ℝ} (hfeas : QbarFeasible G ω f) (θ : ℝ)
    {u v : V} (hu : f u + ω u < θ) (hv : θ + ω v < f v) :
    ¬G.Adj u v := by
  intro h
  have habs := hfeas.edge_constraint u v h
  rw [abs_le] at habs
  linarith [habs.1, habs.2]

/-! ## Key Integral Identities

These are the analytical core of the threshold rounding argument.
They are used in the proof that Q̄(G) ≤ 4n/ψ(G) (Lemma 3.2).
-/

omit [DecidableEq V] in
/-- The integral of slab sizes equals twice the sum of weights:
`∫_ℝ |{v : |f(v) - θ| ≤ ω(v)}| dθ = 2 Σ ω(v)`.

Proof: By Fubini, exchange sum and integral. Each vertex `v` contributes
an interval `[f(v)-ω(v), f(v)+ω(v)]` of length `2ω(v)`. -/
theorem integral_slab_size {ω f : V → ℝ} (hω : ∀ v, 0 ≤ ω v) :
    ∫ (θ : ℝ), (↑(Finset.univ.filter (fun v => |f v - θ| ≤ ω v)).card : ℝ) =
      2 * ∑ v : V, ω v := by
  have h_integral : ∫ θ, (∑ v, (if θ ∈ Set.Icc (f v - ω v) (f v + ω v) then 1 else 0) : ℝ) ∂MeasureTheory.volume = ∑ v, ∫ θ in Set.Icc (f v - ω v) (f v + ω v), (1 : ℝ) ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_congr rfl fun _ _ => by rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
    · intro v _
      rw [MeasureTheory.integrable_congr]
      refine' MeasureTheory.integrable_indicator_iff (measurableSet_Icc) |>.2 _
      exacts [fun _ => 1, f v - ω v, f v + ω v, Continuous.integrableOn_Icc (by continuity), Filter.Eventually.of_forall fun x => by simp +decide [Set.indicator]]
  convert h_integral using 1
  · simp +decide [abs_le , add_comm]
    simp +decide only [and_comm]
  · simp +decide [two_mul, hω]
    rw [Finset.sum_add_distrib]

omit [DecidableEq V] in
/-- The integral of `|A_θ| · |B_θ|` equals half the pairwise absolute
difference sum: `∫_ℝ |{v:f(v)≤θ}|·|{v:θ<f(v)}| dθ = (1/2) Σ|f(u)-f(v)|`.

Proof: By Fubini, each pair `(u,v)` with `f(u) ≤ f(v)` contributes
`f(v) - f(u)` via the integral of `𝟙_{[f(u), f(v))}`. -/
theorem integral_product_sizes (f : V → ℝ) :
    ∫ (θ : ℝ), (↑(Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) *
      (↑(Finset.univ.filter (fun v => θ < f v)).card : ℝ) =
      (1 / 2 : ℝ) * ∑ u : V, ∑ v : V, |f u - f v| := by
  have h_pairs : ∀ θ : ℝ, ((Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) * ((Finset.univ.filter (fun v => θ < f v)).card : ℝ) = ∑ u, ∑ v, (if f u ≤ θ ∧ θ < f v then 1 else 0 : ℝ) := by
    intro θ; rw [Finset.card_filter, Finset.card_filter]; simp +decide
    rw_mod_cast [Finset.card_filter, Finset.card_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.card_filter]; rw [Finset.mul_sum _ _ _]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> aesop
  have h_fubini : ∫ θ : ℝ, ∑ u, ∑ v, (if f u ≤ θ ∧ θ < f v then 1 else 0 : ℝ) = ∑ u, ∑ v, ∫ θ : ℝ, (if f u ≤ θ ∧ θ < f v then 1 else 0 : ℝ) := by
    rw [MeasureTheory.integral_finset_sum]
    · refine' Finset.sum_congr rfl fun u _ => _
      rw [MeasureTheory.integral_finset_sum]
      intro v _; refine' MeasureTheory.Integrable.congr _ _
      refine' fun θ => Set.indicator (Set.Ico (f u) (f v)) (fun _ => 1) θ
      · rw [MeasureTheory.integrable_indicator_iff] <;> norm_num
      · norm_num [Filter.EventuallyEq, Set.indicator]
    · refine' fun u _ => MeasureTheory.integrable_finset_sum _ fun v _ => _
      refine' MeasureTheory.Integrable.congr _ _
      refine' fun θ => Set.indicator (Set.Ico (f u) (f v)) (fun _ => 1) θ
      · rw [MeasureTheory.integrable_indicator_iff] <;> norm_num
      · norm_num [Filter.EventuallyEq, Set.indicator]
  have h_inner : ∀ u v : V, ∫ θ : ℝ, (if f u ≤ θ ∧ θ < f v then 1 else 0 : ℝ) = max 0 (f v - f u) := by
    intro u v
    have h_inner_eval : ∫ θ in Set.Ico (f u) (f v), (1 : ℝ) = max 0 (f v - f u) := by
      cases le_total (f v) (f u) <;> simp +decide [*]
    rw [← h_inner_eval, ← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
  have h_subst : ∑ u, ∑ v, max 0 (f v - f u) = (1 / 2) * ∑ u, ∑ v, |f u - f v| := by
    have h_subst : ∑ u, ∑ v, max 0 (f v - f u) + ∑ u, ∑ v, max 0 (f u - f v) = ∑ u, ∑ v, |f u - f v| := by
      simp +decide only [← sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by cases max_cases (0 : ℝ) (f j - f i) <;> cases max_cases (0 : ℝ) (f i - f j) <;> cases abs_cases (f i - f j) <;> linarith
    linarith [show ∑ u : V, ∑ v : V, max 0 (f u - f v) = ∑ u : V, ∑ v : V, max 0 (f v - f u) by rw [Finset.sum_comm]]
  aesop

/-! ## Vertex Expansion → Balanced Separators (Observation 3.1)

If every induced subgraph `H` on a vertex set `W` with `|W| ≥ 2` admits
a nonempty set `T ⊆ W` with `|T| ≤ |W|/2` and a cover-boundary `C` with
`|C| ≤ α|T|/|W|`, then `G` has a `(2/3)`-balanced separator of size ≤ `α`.

The proof is an iterative peeling argument:
1. While the remaining vertex set has a component of size > `2n/3`:
   find `T`, `C` via the expansion hypothesis
2. Add `C` to the separator, remove `T ∪ C` from the remaining vertices
3. The total separator size is `Σ|Cᵢ| ≤ α·(1/2 + ln(3/2)) < α`
-/

/-! **Observation 3.1** (psi-to-sep). Vertex expansion bounds yield
balanced separators via iterative peeling.

Now proved in `RequestProject.Peeling` as `expansion_to_sep`.
Note: requires `2 ≤ Fintype.card V`. -/

/-! ## Proposition 2.1: Non-Expansive Embeddings Relate Q and Q̄ -/

section SPtoEmbed
variable {V : Type*} [Fintype V]

/-- **Proposition 2.1** (sp-to-embed). A Q̄-feasible pair for a connected
graph has objective value ≤ Q̄(G). -/
theorem sp_to_embed_feasibility (G : SimpleGraph V) (hconn : G.Connected)
    {ω f : V → ℝ} (hfeas : QbarFeasible G ω f) :
    QbarObj f ≤ Qbar G :=
  Qbar_le_of_feasible G hconn hfeas

end SPtoEmbed

/-! ## Proposition 2.2: Q̄ Bounds → Balanced Separators -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Helper Lemmas for embed_to_sep -/

/-
A graph on 0 vertices has a balanced separator.
-/
lemma hasBalancedSep_of_card_zero (G : SimpleGraph V) (k : ℝ) (hk : 0 ≤ k)
    (hn : Fintype.card V = 0) :
    G.HasBalancedSeparator (2/3) k := by
  -- Since � the� graph is empty, we can choose S = ∅.
  use ∅; simp [];
  rw [ Fintype.card_eq_zero_iff ] at hn;
  simp +decide [ SimpleGraph.IsBalancedSeparator ];
  exact hk

/-
Q̄ of a single-vertex graph is 0.
-/
omit [DecidableEq V] in
lemma qbar_single_vertex (G : SimpleGraph V) (hn : Fintype.card V = 1) :
    Qbar G = 0 := by
  convert csSup_singleton ( 0 : ℝ );
  unfold Qbar;
  congr;
  ext; simp [QbarObj];
  rw [ Fintype.card_eq_one_iff ] at hn; obtain ⟨ v, hv ⟩ := hn; simp +decide [ hv ] ;
  exact ⟨ fun h => h.2, fun h => ⟨ ⟨ fun _ => 0, fun _ => 0, by constructor <;> simp +decide [ hv ] ⟩, h ⟩ ⟩

omit [Fintype V] in
/-- If the induced subgraph on `W` is disconnected, there exists a nonempty
    T ⊆ W with |T| ≤ |W|/2 and no edges from T to W \ T. -/
lemma exists_small_closed_subset_of_not_connected
    (G : SimpleGraph V) (W : Finset V)
    (hW : 2 ≤ W.card) (hnotconn : ¬(G.induce (↑W : Set V)).Connected) :
    ∃ T : Finset V, T ⊆ W ∧ T.Nonempty ∧ 2 * T.card ≤ W.card ∧
      ∀ u ∈ T, ∀ v ∈ W, v ∉ T → ¬G.Adj u v := by
  have hne : Nonempty {w : V // w ∈ (↑W : Set V)} := by
    rw [← Fintype.card_pos_iff]; simp only [Finset.coe_sort_coe, Fintype.card_coe]; omega
  have hnp : ¬(G.induce (↑W : Set V)).Preconnected := by
    intro hp; exact hnotconn (SimpleGraph.Connected.mk hp)
  simp only [SimpleGraph.Preconnected] at hnp; push_neg at hnp
  obtain ⟨u, v, hnr⟩ := hnp
  classical
  let T₀ := W.filter (fun w => ∃ (hw : w ∈ (↑W : Set V)),
    (G.induce (↑W : Set V)).Reachable u ⟨w, hw⟩)
  have hT₀W : T₀ ⊆ W := Finset.filter_subset _ W
  have hT₀u : u.val ∈ T₀ := by
    simp only [T₀, Finset.mem_filter]
    exact ⟨u.prop, u.prop, SimpleGraph.Reachable.refl u⟩
  have hT₀v : v.val ∉ T₀ := by
    simp only [T₀, Finset.mem_filter]; push_neg
    intro _ hw; convert hnr
  have hT₀closed : ∀ w ∈ T₀, ∀ w' ∈ W, w' ∉ T₀ → ¬G.Adj w w' := by
    intro w hw w' hw' hw'T hadj
    apply hw'T
    simp only [T₀, Finset.mem_filter] at hw ⊢
    obtain ⟨_, hwW, hr⟩ := hw
    refine ⟨hw', hw', hr.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.induce_adj]; exact hadj
  have hT₀ne : T₀.Nonempty := ⟨u.val, hT₀u⟩
  have hT₀proper : T₀.card < W.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hT₀W, fun h => hT₀v ?_⟩
    rw [h]; exact Finset.mem_coe.mp v.prop
  by_cases hsize : 2 * T₀.card ≤ W.card
  · exact ⟨T₀, hT₀W, hT₀ne, hsize, hT₀closed⟩
  · push_neg at hsize
    refine ⟨W \ T₀, Finset.sdiff_subset,
      ⟨v.val, Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp v.prop, hT₀v⟩⟩, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset hT₀W]; omega
    · intro w hw w' hw' hw'T hadj
      have hwT : w ∉ T₀ := (Finset.mem_sdiff.mp hw).2
      have : w' ∈ T₀ := by
        by_contra h; exact hw'T (Finset.mem_sdiff.mpr ⟨hw', h⟩)
      exact absurd (G.adj_symm hadj) (hT₀closed w' this w (Finset.sdiff_subset hw) hwT)

omit [Fintype V] in
/-- If the induced subgraph on `W` is disconnected, the expansion pair exists
    with C = ∅ (no separator cost). -/
lemma disconnected_has_expansion_pair
    (G : SimpleGraph V) (W : Finset V)
    (hW : 2 ≤ W.card) (hnotconn : ¬(G.induce (↑W : Set V)).Connected)
    (α : ℝ) (hα : 0 < α) :
    ∃ (T C : Finset V), T ⊆ W ∧ C ⊆ W ∧ T.Nonempty ∧ 2 * T.card ≤ W.card ∧
      (∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C) ∧
      (C.card : ℝ) ≤ α * T.card / W.card := by
  obtain ⟨T, hTW, hTne, hTcard, hTclosed⟩ := exists_small_closed_subset_of_not_connected G W hW hnotconn
  exact ⟨T, ∅, hTW, Finset.empty_subset W, hTne, hTcard,
    fun u v hadj hu hv hvT => absurd hadj (hTclosed u hu v hv hvT),
    by simp; exact div_nonneg (mul_nonneg hα.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)⟩

/-- The slab at threshold θ is an IsEdgeCutCover for {v | f v ≤ θ}. -/
lemma slab_is_edge_cut_cover {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    {ω f : W → ℝ} (hfeas : QbarFeasible H ω f) (θ : ℝ) :
    H.IsEdgeCutCover
      (Finset.univ.filter (fun v => f v ≤ θ))
      (Finset.univ.filter (fun v => |f v - θ| ≤ ω v)) := by
  intro u v hadj hu hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv ⊢
  push_neg at hv
  by_contra h; push_neg at h; obtain ⟨hu', hv'⟩ := h
  have h1 : f u + ω u < θ := by rw [abs_of_nonpos (by linarith)] at hu'; linarith
  have h2 : θ + ω v < f v := by rw [abs_of_pos (by linarith)] at hv'; linarith
  have := hfeas.edge_constraint u v hadj; rw [abs_le] at this; linarith [this.1, this.2]

omit [Fintype V] in
omit [Fintype V] in
/-- coverBoundarySize is at most the card of any valid cover. -/
lemma coverBoundarySize_le_of_cover {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (S C : Finset W) (hC : H.IsEdgeCutCover S C) :
    H.coverBoundarySize S ≤ C.card := by
  exact Nat.sInf_le ⟨C, rfl, hC⟩

/-
Pointwise bound: slab size ≥ (c/n) * |left| * |right| at every threshold.
-/
lemma slab_ge_expansion_times_product {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c)
    (hexp : ∀ (S : Finset W), S.Nonempty → 2 * S.card ≤ Fintype.card W →
      c * S.card ≤ H.coverBoundarySize S)
    {ω f : W → ℝ} (hfeas : QbarFeasible H ω f) (θ : ℝ) :
    c / Fintype.card W *
      ((Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) *
      ((Finset.univ.filter (fun v => θ < f v)).card : ℝ) ≤
    ((Finset.univ.filter (fun v => |f v - θ| ≤ ω v)).card : ℝ) := by
  by_cases hW : Fintype.card W = 0;
  · aesop;
  · -- Let $L = \{v : W \mid f(v) \leq � \�theta\}$ and $R � =� \{v : W \mid \theta < f �(v�)\}$.
    set L := Finset.univ.filter (fun v => f v ≤ θ)
    set R := Finset.univ.filter (fun v => θ < f v);
    -- By assumption, $c * |L| \leq |S|$ if $|L| \leq n/2$, and $c * |R| \leq |S|$ if $|R| \leq n/2$.
    have h_case : (c * L.card : ℝ) ≤ (Finset.univ.filter (fun v => |f v - θ| ≤ ω v)).card ∨ (c * R.card : ℝ) ≤ (Finset.univ.filter (fun v => |f v - θ| ≤ ω v)).card := by
      by_cases hL : L.Nonempty ∧ 2 * L.card ≤ Fintype.card W;
      · refine' Or.inl ( le_trans ( hexp L hL.1 hL.2 ) _ );
        exact_mod_cast coverBoundarySize_le_of_cover H L _ ( slab_is_edge_cut_cover H hfeas θ );
      · by_cases hR : R.Nonempty ∧ 2 * R.card ≤ Fintype.card W;
        · refine' Or.inr ( le_trans ( hexp R hR.1 hR.2 ) _ );
          refine' mod_cast coverBoundarySize_le_of_cover _ _ _ _;
          intro u v huv hu hv;
          grind +splitIndPred;
        · by_cases hL : L.Nonempty <;> by_cases hR : R.Nonempty <;> simp_all +decide;
          have h_union : L.card + R.card = Fintype.card W := by
            rw [ Finset.card_filter, Finset.card_filter ];
            rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun _ _ => by aesop, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one ];
          linarith;
    cases' h_case with h_case h_case;
    · rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ ];
      · exact mul_le_mul h_case ( mod_cast by simpa using Finset.card_le_univ R ) ( by positivity ) ( by positivity );
      · positivity;
    · refine' le_trans _ h_case;
      field_simp;
      exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( mod_cast Finset.card_le_univ _ ) hc ) ( Nat.cast_nonneg _ )

/-
For any feasible (ω,f) for a connected graph H on n vertices,
    if every nonempty S with |S| ≤ n/2 has coverBoundarySize(S) ≥ c|S|,
    then QbarObj(f) ≤ 4n/c.
-/
lemma qbar_obj_bound_from_expansion {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (c : ℝ) (hc : 0 < c)
    (hexp : ∀ (S : Finset W), S.Nonempty → 2 * S.card ≤ Fintype.card W →
      c * S.card ≤ H.coverBoundarySize S)
    {ω f : W → ℝ} (hfeas : QbarFeasible H ω f) :
    QbarObj f ≤ 4 * Fintype.card W / c := by
  -- Apply the integral identities and the pointwise bound to derive the inequality.
  have h_integral : ∫ θ : ℝ, ((Finset.univ.filter (fun v => |f v - θ| ≤ ω v)).card : ℝ) - (c / Fintype.card W) * ((Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) * ((Finset.univ.filter (fun v => θ < f v)).card : ℝ) ≥ 0 := by
    refine' MeasureTheory.integral_nonneg fun θ => sub_nonneg_of_le _;
    -- Apply the pointwise bound from `h_pointwise`.
    apply slab_ge_expansion_times_product H c hc.le hexp hfeas θ;
  contrapose! h_integral;
  by_cases hW : Fintype.card W = 0 <;> simp_all +decide [ division_def ];
  · simp_all +decide [ Fintype.card_eq_zero_iff ];
    exact h_integral.ne' ( by unfold QbarObj; aesop );
  · rw [ MeasureTheory.integral_sub ];
    · simp +decide [ mul_assoc, MeasureTheory.integral_const_mul , integral_slab_size, integral_product_sizes, hfeas.omega_nonneg ];
      field_simp at h_integral;
      rw [ inv_mul_eq_div, mul_div, lt_div_iff₀ ] <;> first | positivity | norm_num [ QbarObj ] at * ; nlinarith [ hfeas.omega_sum ] ;
    · have h_integrable : MeasureTheory.Integrable (fun θ : ℝ => (∑ v : W, (if |f v - θ| ≤ ω v then 1 else 0) : ℝ)) MeasureTheory.volume := by
        refine' MeasureTheory.integrable_finset_sum _ _;
        intro i _;
        refine' MeasureTheory.integrable_indicator_iff ( measurableSet_le ( measurable_norm.comp ( measurable_const.sub measurable_id' ) ) measurable_const ) |>.2 _;
        simp +decide [  ];
        exact lt_of_le_of_lt ( MeasureTheory.measure_mono ( show { a : ℝ | |f i - a| ≤ ω i } ⊆ Set.Icc ( f i - ω i ) ( f i + ω i ) from fun x hx => ⟨ by linarith [ abs_le.mp hx.out ], by linarith [ abs_le.mp hx.out ] ⟩ ) ) ( by simp +decide [ Real.volume_Icc ] );
      aesop;
    · have h_integrable : MeasureTheory.Integrable (fun θ : ℝ => ((Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) * ((Finset.univ.filter (fun v => θ < f v)).card : ℝ)) MeasureTheory.volume := by
        have h_integrable : ∫ θ : ℝ, ((Finset.univ.filter (fun v => f v ≤ θ)).card : ℝ) * ((Finset.univ.filter (fun v => θ < f v)).card : ℝ) = (1 / 2 : ℝ) * ∑ u : W, ∑ v : W, |f u - f v| := by
          convert integral_product_sizes f using 1;
        exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at h_integrable; exact absurd h_integrable ( by exact ne_of_lt ( mul_pos ( by norm_num ) ( lt_of_le_of_lt ( by positivity ) h_integral ) ) ) );
      convert h_integrable.const_mul ( c * ( Fintype.card W : ℝ ) ⁻¹ ) using 2 ; ring

/-
If the induced subgraph on `W` is connected with `Q̄ ≥ |W|²/β`, then
    there exists nonempty S (in the subtype) with |S| ≤ n/2 and
    coverBoundarySize(S) ≤ 4β|S|/n.
-/
lemma exists_expansion_pair_subtype
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (_hconn : H.Connected)
    (n : ℕ) (hn : n = Fintype.card W) (hn2 : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β)
    (hQ : (n : ℝ) ^ 2 / β ≤ Qbar H) :
    ∃ (S : Finset W), S.Nonempty ∧ 2 * S.card ≤ n ∧
      (H.coverBoundarySize S : ℝ) ≤ 4 * β * S.card / n := by
  by_contra! h_contra;
  -- Apply qbar_obj_bound_from_expansion with c = c₀, hc = (c₀ > 4β/n > 0), and hexp from above:
  set c₀ := sInf (Set.image (fun S : Finset W => (H.coverBoundarySize S : ℝ) / S.card) {S : Finset W | S.Nonempty ∧ 2 * S.card ≤ n})
  have hc₀_pos : 0 < c₀ := by
    have hc₀_pos : ∀ S : Finset W, S.Nonempty → 2 * S.card ≤ n → 4 * β / n < (H.coverBoundarySize S : ℝ) / S.card := by
      intro S hS hS'; specialize h_contra S hS hS'; rw [ lt_div_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr hS ) ] ; convert h_contra using 1 ; ring;
    refine' lt_of_lt_of_le _ ( le_csInf _ _ );
    exact div_pos ( mul_pos zero_lt_four hβ ) ( Nat.cast_pos.mpr ( by linarith : 0 < n ) );
    · refine' ⟨ _, ⟨ { Classical.choose ( Finset.card_pos.mp ( by linarith : 0 < Fintype.card W ) ) }, ⟨ _, _ ⟩, rfl ⟩ ⟩ <;> simp +decide [ hn ];
      linarith;
    · grind +splitIndPred
  have hc₀_le : ∀ S : Finset W, S.Nonempty → 2 * S.card ≤ n → c₀ * S.card ≤ H.coverBoundarySize S := by
    intro S hS₁ hS₂; exact le_trans ( mul_le_mul_of_nonneg_right ( csInf_le ( by exact Set.Finite.bddBelow <| Set.toFinite _ ) <| Set.mem_image_of_mem _ ⟨ hS₁, hS₂ ⟩ ) <| Nat.cast_nonneg _ ) <| by rw [ div_mul_cancel₀ _ <| Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr hS₁ ] ;
  have hQbar_le : Qbar H ≤ 4 * n / c₀ := by
    have hQbar_le : ∀ f : W → ℝ, ∀ ω : W → ℝ, QbarFeasible H ω f → QbarObj f ≤ 4 * n / c₀ := by
      grind +suggestions;
    exact csSup_le ⟨ _, ⟨ 0, 0, ⟨ by norm_num, by norm_num, by norm_num ⟩, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ ω, f, hfeas, rfl ⟩ ; exact hQbar_le f ω hfeas;
  -- Since $c₀ > 4β/n$, we have $4n/c₀ < n²/β$.
  have hc₀_gt : c₀ > 4 * β / n := by
    -- Since $c₀$ is the infimum of the set, there exists some $S$ in the set such that $c₀ \leq (H.coverBoundarySize S : ℝ) / S.card$.
    obtain ⟨S, hS⟩ : ∃ S : Finset W, S.Nonempty ∧ 2 * S.card ≤ n ∧ c₀ = (H.coverBoundarySize S : ℝ) / S.card := by
      have hc₀_eq : c₀ ∈ Set.image (fun S : Finset W => (H.coverBoundarySize S : ℝ) / S.card) {S : Finset W | S.Nonempty ∧ 2 * S.card ≤ n} := by
        apply_rules [ IsCompact.sInf_mem ];
        · exact Set.Finite.isCompact ( Set.toFinite _ );
        · exact ⟨ _, ⟨ { Classical.choose ( Finset.card_pos.mp ( by linarith : 0 < Fintype.card W ) ) }, ⟨ Finset.singleton_nonempty _, by simpa using by linarith ⟩, rfl ⟩ ⟩;
      grind;
    have := h_contra S hS.1 hS.2.1;
    rw [ hS.2.2, gt_iff_lt, div_lt_div_iff₀ ] at * <;> nlinarith [ show ( S.card : ℝ ) > 0 from Nat.cast_pos.mpr hS.1.card_pos, show ( n : ℝ ) > 0 from Nat.cast_pos.mpr ( by linarith ), mul_div_cancel₀ ( 4 * β * ( S.card : ℝ ) ) ( by positivity : ( n : ℝ ) ≠ 0 ) ]
  have hQbar_lt : 4 * n / c₀ < n ^ 2 / β := by
    field_simp;
    rwa [ gt_iff_lt, div_lt_iff₀' ( by positivity ) ] at hc₀_gt
  linarith [hQ, hQbar_le, hQbar_lt]

/-
If the induced subgraph on `W` is connected with `Q̄ ≥ |W|²/β`, then
    the expansion pair exists with `|C| ≤ 4β|T|/|W|`.
-/
omit [Fintype V] in
lemma connected_qbar_has_expansion_pair
    (G : SimpleGraph V) (W : Finset V)
    (hW : 2 ≤ W.card) (hconn : (G.induce (↑W : Set V)).Connected)
    (β : ℝ) (hβ : 0 < β)
    (hQbar : (W.card : ℝ) ^ 2 / β ≤ Qbar (G.induce (↑W : Set V))) :
    ∃ (T C : Finset V), T ⊆ W ∧ C ⊆ W ∧ T.Nonempty ∧ 2 * T.card ≤ W.card ∧
      (∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C) ∧
      (C.card : ℝ) ≤ (4 * β) * T.card / W.card := by
  -- Apply the lemma `exists_expansion_pair_subtype` to the induced subgraph on ` �W�`.
  obtain ⟨S, hSne, hScard, hScover⟩ := exists_expansion_pair_subtype (G.induce (↑W : Set V)) hconn W.card (by simp [Fintype.card_coe]) hW β hβ hQbar;
  -- Get the minimum cover. Since coverBoundarySize S is the sInf of a nonempty ℕ-set (Finset.univ is a valid cover: � ∀� u v, H.Adj u v → u ∈ S → v S → u ∈ Finset.univ v ∈ Finset.univ), use Nat.sInf_mem to get C₀ : Finset {v // v ∈ ↑W} with |C₀| = coverBoundarySize S and H.IsEdgeCutCover S C₀.
  obtain ⟨C₀, hC₀card, hC₀cover⟩ : ∃ C₀ : Finset (↥W), C₀.card = (G.induce (↑W : Set V)).coverBoundarySize S ∧ (G.induce (↑W : Set V)).IsEdgeCutCover S C₀ := by
    have h_nonempty : { c | ∃ C : Finset (↥W), C.card = c ∧ (G.induce (↑W : Set V)).IsEdgeCutCover S C }.Nonempty := by
      use W.card;
      use Finset.univ; simp [SimpleGraph.IsEdgeCutCover];
    exact Nat.sInf_mem h_nonempty;
  refine' ⟨ Finset.image Subtype.val S, Finset.image Subtype.val C₀, _, _, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · rwa [ Finset.card_image_of_injective _ Subtype.coe_injective ];
  · exact fun u v huv hu huS hv hvS => hC₀cover _ _ huv huS hvS;
  · rw [ Finset.card_image_of_injective _ Subtype.coe_injective, Finset.card_image_of_injective _ Subtype.coe_injective ] ; aesop

/-- **Proposition 2.2** (embed-to-sep).

If every connected induced subgraph `H` of `G` with `n'` vertices has
`Q̄(H) ≥ (n')² / β`, then `G` admits a `(2/3)`-balanced vertex separator
of size at most `4β`.

Proof sketch:
1. By the Q̄ upper bound (integral argument): for connected `H`,
   `ψ(H) ≤ 4n'/Q̄(H) ≤ 4β/n'`
2. The expansion bound extends to all induced subgraphs by working
   within connected components
3. By `expansion_to_sep`, `G` has a `(2/3)`-balanced separator of size ≤ `4β` -/
theorem embed_to_sep (G : SimpleGraph V) (β : ℝ) (hβ : 0 < β)
    (hQbar : ∀ (S : Finset V), S.Nonempty →
      (G.induce (↑S : Set V)).Connected →
      ((S.card : ℝ)^2 / β ≤ Qbar (G.induce (↑S : Set V)))) :
    G.HasBalancedSeparator (2/3) (4 * β) := by
  by_cases hn : 2 ≤ Fintype.card V
  · apply expansion_to_sep G (4 * β) (by linarith) hn
    intro W hW
    by_cases hconn : (G.induce (↑W : Set V)).Connected
    · exact connected_qbar_has_expansion_pair G W hW hconn β hβ
        (hQbar W (Finset.card_pos.mp (by omega)) hconn)
    · exact disconnected_has_expansion_pair G W hW hconn (4 * β) (by linarith)
  · push_neg at hn
    -- |V| ≤ 1
    by_cases hn0 : Fintype.card V = 0
    · exact hasBalancedSep_of_card_zero G (4 * β) (by linarith) hn0
    · -- |V| = 1: hQbar gives contradiction
      exfalso
      have h1 : Fintype.card V = 1 := by omega
      haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      have hS : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
      have hconn : (G.induce (↑(Finset.univ : Finset V) : Set V)).Connected := by
        haveI : Subsingleton {v : V // v ∈ (↑(Finset.univ : Finset V) : Set V)} := by
          rw [← Fintype.card_le_one_iff_subsingleton]; simp [h1]
        haveI : Nonempty {v : V // v ∈ (↑(Finset.univ : Finset V) : Set V)} := by
          rw [← Fintype.card_pos_iff]; simp [h1]
        exact SimpleGraph.Connected.of_subsingleton
      have hQ := hQbar Finset.univ hS hconn
      simp [Finset.card_univ, h1] at hQ
      have hcard1 : Fintype.card {v : V // v ∈ (↑(Finset.univ : Finset V) : Set V)} = 1 := by
        simp [h1]
      have hQ0 := qbar_single_vertex (G.induce (↑(Finset.univ : Finset V) : Set V)) hcard1
      have : 0 < β⁻¹ := inv_pos.mpr hβ
      linarith

/-! ## Main "Putting It All Together" Result -/

/-- **Main Combination Theorem**.

If every connected induced subgraph of `G` has Q̄ ≥ `n'² / β`,
then `G` admits a `(2/3)`-balanced vertex separator of size ≤ `4β`.

In the paper's Theorem 1.3, for `K_h^{(1)}`-induced-minor-free graphs:
  - `Q(H) ≥ (n')²/(49h√m)` (Korhonen-Lokshtanov, Prop 2.3)
  - Distortion ≤ `min{O(log n), 625h²}` (Theorem 1.5)
  - Combined: separator size ≤ `min{O(log n), 122500h²} · h · √m` -/
theorem Qbar_bound_gives_separator (G : SimpleGraph V) (β : ℝ) (hβ : 0 < β)
    (hQbar : ∀ (S : Finset V), S.Nonempty →
      (G.induce (↑S : Set V)).Connected →
      (S.card : ℝ)^2 / β ≤ Qbar (G.induce (↑S : Set V))) :
    G.HasBalancedSeparator (2/3) (4 * β) :=
  embed_to_sep G β hβ hQbar