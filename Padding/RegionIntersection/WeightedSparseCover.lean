/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.RegionIntersection.WeightedLabeling
import Padding.RegionIntersection.WeightedMetricSpace
import Padding.Defs.SparseCover
import Padding.SparseCover.ToPaddedDecomp
import Mathlib

/-! # Sparse cover of the vertex-weighted metric

Using the combined labelling of the grown-region graph `G^ρ`, we build, for each scale `Δ`,
a sparse cover of the vertex-weighted shortest-path metric.  The clusters are:

* the **enlarged components** of the labelling — for each `≈`-class `q` of low-weight
  vertices, the set of points within weighted distance `r` of some member of `q`;
* the **singletons** `{v}` for each high-weight vertex `v` (weight `> ρ`), which are isolated
  at scale `ρ`.

The diameter (`combined_diam`), separation (`combined_separation`), and the weight bounds give
the three sparse-cover properties (bounded diameter, padding, bounded overlap).
-/

open SimpleGraph BandPartition Set Metric
open scoped Classical

noncomputable section

universe u

namespace WeightedRIG

variable {V₁ V₂ : Type u} [Fintype V₁] {G : SimpleGraph V₁} {H : SimpleGraph V₂}
  {μ : RegionIntersectionModel G H} {t : ℕ} {w : V₁ → ℝ} {ρ : ℝ}
  (ht : 2 ≤ t) (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ)

/-- The high-weight vertices (weight `> ρ`). -/
def highWeightSet (w : V₁ → ℝ) (ρ : ℝ) : Set V₁ := {v | ρ < w v}

/-- The component equivalence on low-weight vertices. -/
def compSetoid (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) :
    Setoid ↥(lowWeightSet w ρ) where
  r := compRel μ t ht hH hw hρ
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => compRel_symm ht hH hw hρ h,
    fun h1 h2 => h1.trans h2⟩

/-- The cluster index type: component classes plus high-weight singletons. -/
def clusterIndex (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) : Type u :=
  Quotient (compSetoid μ t ht hH hw hρ) ⊕ ↥(highWeightSet w ρ)

noncomputable instance instFintypeClusterIndex :
    Fintype (clusterIndex μ t ht hH hw hρ) := by
  classical
  unfold clusterIndex
  haveI : Fintype (Quotient (compSetoid μ t ht hH hw hρ)) :=
    Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective
  infer_instance

/-- The cluster labelling lifted to component classes. -/
def groupLabel (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) :
    Quotient (compSetoid μ t ht hH hw hρ) → Fin (2 ^ (t - 2)) :=
  Quotient.lift (lbl μ t ht hH hw hρ) (fun _ _ hab => compRel_label_eq ht hH hw hρ hab)

/-- The clusters of the sparse cover, at padding radius `r`. -/
def grownCluster (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t)
    (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) (r : ℝ) :
    clusterIndex μ t ht hH hw hρ → Set V₁
  | Sum.inl q => {z : V₁ | ∃ x : ↥(lowWeightSet w ρ),
      Quotient.mk (compSetoid μ t ht hH hw hρ) x = q ∧ G.weightedDist w z x.1 ≤ r}
  | Sum.inr y => {y.1}

/-
**Bounded diameter** (in `d_w`): all points of a cluster are within `Δ`.
-/
omit [Fintype V₁] in
lemma grownCluster_dw_diam (hconn : G.Preconnected) {r Δ : ℝ} (hrho : 0 < ρ) (hrnn : 0 ≤ r)
    (hdiam : ((4 * (t - 1) * 1 + 2 : ℕ) : ℝ) * (4 * ρ) + 2 * r ≤ Δ)
    (i : clusterIndex μ t ht hH hw hρ)
    {z z' : V₁} (hz : z ∈ grownCluster μ t ht hH hw hρ r i)
    (hz' : z' ∈ grownCluster μ t ht hH hw hρ r i) :
    G.weightedDist w z z' ≤ Δ := by
  rcases i with ( i | i ) <;> simp_all +decide [grownCluster];
  · obtain ⟨ a, ⟨ ha, rfl ⟩, hz ⟩ := hz
    obtain ⟨ a', ⟨ ha', ha'' ⟩, hz' ⟩ := hz'
    have h_comp : compRel μ t ht hH hw hρ ⟨a, ha⟩ ⟨a', ha'⟩ := by
      have hq := Quotient.exact ha''
      first
        | exact hq
        | exact compRel_symm ht hH hw hρ hq
    have h_triangle : G.weightedDist w z z' ≤ G.weightedDist w z a + G.weightedDist w a a' + G.weightedDist w a' z' := by
      exact le_trans ( SimpleGraph.weightedDist_triangle hw hconn _ _ _ ) ( add_le_add ( SimpleGraph.weightedDist_triangle hw hconn _ _ _ ) le_rfl );
    have h_combined : G.weightedDist w a a' ≤ (4 * (t - 1) * 1 + 2 : ℕ) * (4 * ρ) := by
      convert combined_diam ht hH hw hρ hconn h_comp using 1;
    have h_symm : G.weightedDist w a' z' = G.weightedDist w z' a' :=
      SimpleGraph.weightedDist_comm a' z'
    grind;
  · exact le_trans ( SimpleGraph.weightedDist_self hw _ |> le_of_eq ) ( by nlinarith )

/-
**Padding**: every point's `r`-ball is contained in some cluster.
-/
omit [Fintype V₁] in
lemma grownCluster_padding (hconn : G.Preconnected) {r : ℝ} (hrρ : r < ρ)
    (v : V₁) :
    ∃ i : clusterIndex μ t ht hH hw hρ, ∀ z : V₁,
      G.weightedDist w v z ≤ r → z ∈ grownCluster μ t ht hH hw hρ r i := by
  by_cases hv : v ∈ lowWeightSet w ρ;
  · use Sum.inl (Quotient.mk (compSetoid μ t ht hH hw hρ) ⟨v, hv⟩);
    intro z hz;
    exact ⟨ ⟨ v, hv ⟩, rfl, by simpa only [ SimpleGraph.weightedDist_comm ] using hz ⟩;
  · refine' ⟨ Sum.inr ⟨ v, _ ⟩, _ ⟩ <;> simp_all +decide [ lowWeightSet, highWeightSet, grownCluster ];
    intro z hz;
    by_contra hne;
    exact hv ( by exact le_trans ( SimpleGraph.weight_le_weightedDist hw ( hconn v z ) ( Ne.symm hne ) ) ( hz.trans hrρ.le ) )

/-
**Sparsity**: each point lies in at most `2^{t-2} + 1` clusters.
-/
lemma grownCluster_sparse (hconn : G.Preconnected) {r : ℝ} (h2r : 2 * r < ρ)
    (v : V₁) :
    (Finset.univ.filter (fun i : clusterIndex μ t ht hH hw hρ =>
      v ∈ grownCluster μ t ht hH hw hρ r i)).card ≤ 2 ^ (t - 2) + 1 := by
  -- Define the function f from clusterIndex to Fin (2^(t-2)) ⊕ Unit.
  set f : clusterIndex μ t ht hH hw hρ → Fin (2 ^ (t - 2)) ⊕ Unit := fun i => match i with
    | Sum.inl q => Sum.inl (groupLabel μ t ht hH hw hρ q)
    | Sum.inr y => Sum.inr ();
  have h_inj : ∀ i j : clusterIndex μ t ht hH hw hρ, f i = f j → v ∈ grownCluster μ t ht hH hw hρ r i → v ∈ grownCluster μ t ht hH hw hρ r j → i = j := by
    rintro ( i | i ) ( j | j ) <;> simp +decide [ f ];
    · intro hij hv hv';
      obtain ⟨ x, hx, hx' ⟩ := hv
      obtain ⟨ y, hy, hy' ⟩ := hv';
      contrapose! h2r;
      have h_combined : ρ ≤ G.weightedDist w x.1 y.1 := by
        apply combined_separation;
        all_goals try assumption;
        · unfold groupLabel at hij; aesop;
        · intro hxy;
          exact h2r ( by rw [ show i = j from by rw [ ← hx, ← hy ] ; exact Quotient.sound hxy ] );
      have h_triangle : G.weightedDist w x.1 y.1 ≤ G.weightedDist w x.1 v + G.weightedDist w v y.1 := by
        grind +suggestions;
      linarith [ SimpleGraph.weightedDist_comm ( G := G ) ( w := w ) v x.1, SimpleGraph.weightedDist_comm ( G := G ) ( w := w ) v y.1 ];
    · unfold grownCluster; aesop;
  convert Finset.card_le_card_of_injOn f ( fun x _ => Finset.mem_univ _ ) ( fun x hx y hy hxy => h_inj x y hxy ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 ) ) using 1;
  simp +decide [ Finset.card_univ ]

/-- **Vertex-weighted region-intersection graphs admit a sparse cover scheme.**
For a region intersection model of `G` over a `Kₜ`-minor-free host `H` (with `t ≥ 2`), the
vertex-weighted shortest-path metric admits a `(3(16(t-1)+9), 2^{t-2}+1)`-sparse cover
scheme. -/
theorem weighted_admits_sparse_cover_scheme
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected) :
    @AdmitsSparseCoverScheme V₁ (G.weightedPseudoMetricSpace w hw hconn)
      ((3 * (16 * (t - 1) + 9) : ℕ) : ℝ) (2 ^ (t - 2) + 1) := by
  classical
  intro Δ hΔ
  letI inst := G.weightedPseudoMetricSpace w hw hconn
  have hdpos : (0:ℝ) < ((16 * (t - 1) + 9 : ℕ) : ℝ) := by
    have : 0 < 16 * (t - 1) + 9 := by omega
    exact_mod_cast this
  set d : ℝ := ((16 * (t - 1) + 9 : ℕ) : ℝ) with hd
  have hdne : d ≠ 0 := ne_of_gt hdpos
  set ρ : ℝ := Δ / d with hρdef
  have ρpos : 0 < ρ := div_pos hΔ hdpos
  have hρ0 : 0 ≤ ρ := ρpos.le
  set r : ℝ := ρ / 3 with hrdef
  have rpos : 0 < r := by positivity
  have hn1 : (1:ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by
    have : 1 ≤ t - 1 := by omega
    exact_mod_cast this
  have hΔeq : Δ = ρ * d := by rw [hρdef]; field_simp
  have hβr : Δ / ((3 * (16 * (t - 1) + 9) : ℕ) : ℝ) = r := by
    rw [hrdef, hρdef, hd]; push_cast; field_simp
  have hdiam : ((4 * (t - 1) * 1 + 2 : ℕ) : ℝ) * (4 * ρ) + 2 * r ≤ Δ := by
    have h3r : ρ = 3 * r := by rw [hrdef]; ring
    rw [hd] at hΔeq
    push_cast at hΔeq ⊢
    nlinarith [ρpos, rpos, hn1, hΔeq, h3r]
  refine ⟨{
    ι := clusterIndex μ t ht hH hw hρ0
    finι := inferInstance
    cluster := grownCluster μ t ht hH hw hρ0 r
    diam_le := ?_
    padding := ?_
    sparse := ?_ }⟩
  · intro i
    refine Metric.diam_le_of_forall_dist_le hΔ.le (fun x hx y hy => ?_)
    exact grownCluster_dw_diam ht hH hw hρ0 hconn ρpos rpos.le hdiam i hx hy
  · intro v
    obtain ⟨i, hi⟩ := grownCluster_padding ht hH hw hρ0 hconn (by linarith : r < ρ) v
    refine ⟨i, ?_⟩
    rw [hβr]
    intro z hz
    rw [Metric.mem_closedBall] at hz
    exact hi z (by rw [SimpleGraph.weightedDist_comm]; exact hz)
  · intro v
    exact grownCluster_sparse ht hH hw hρ0 hconn (by linarith : 2 * r < ρ) v

/-- **Padded decompositions of vertex-weighted region intersection graphs, with explicit
minor-size dependence.**
For a region intersection model of `G` over a `Kₜ`-minor-free host `H` (with `t ≥ 2`) and any
nonnegative vertex weights, the vertex-weighted shortest-path metric admits a padded
decomposition scheme with the constants produced directly by the sparse-cover conversion. -/
theorem weighted_rig_admits_padded_explicit
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected) :
    @PaddedDecomposition.AdmitsPaddedDecompScheme V₁
      (G.weightedPseudoMetricSpace w hw hconn)
      (4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) *
        (2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ))))
      (1 / (4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)))) := by
  classical
  letI inst := G.weightedPseudoMetricSpace w hw hconn
  set β : ℝ := ((3 * (16 * (t - 1) + 9) : ℕ) : ℝ) with hβ
  set s : ℕ := 2 ^ (t - 2) + 1 with hs
  have hβpos : 0 < β := by
    have : 0 < 3 * (16 * (t - 1) + 9) := by omega
    rw [hβ]; exact_mod_cast this
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.le_add_left 1 _
  have hsc : @AdmitsSparseCoverScheme V₁ inst β s := by
    simpa [hβ, hs] using weighted_admits_sparse_cover_scheme μ t ht hH w hw hconn
  have hbdd : ∀ Δ > 0, ∀ cover : @SparseCover V₁ inst β s Δ, ∀ i,
      Bornology.IsBounded (cover.cluster i) := by
    intro Δ _ cover i
    exact (Set.toFinite (cover.cluster i)).isBounded
  have hpad := sparse_cover_scheme_to_padded_decomp_scheme V₁ β s hβpos hs1 hsc hbdd
  simpa [hβ, hs] using hpad

/-- **Padded decompositions of vertex-weighted region intersection graphs.**
Existential wrapper around `weighted_rig_admits_padded_explicit`. -/
theorem weighted_rig_admits_padded
    (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (w : V₁ → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected) :
    ∃ (β δ₀ : ℝ), 0 < β ∧ 0 < δ₀ ∧
      @PaddedDecomposition.AdmitsPaddedDecompScheme V₁
        (G.weightedPseudoMetricSpace w hw hconn) β δ₀ := by
  refine ⟨4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) *
      (2 + 2 * Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ))),
    1 / (4 * (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ))), ?_, ?_,
    weighted_rig_admits_padded_explicit μ t ht hH w hw hconn⟩
  · have hβpos : 0 < (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) := by
      have : 0 < 3 * (16 * (t - 1) + 9) := by omega
      exact_mod_cast this
    have hlog : 0 ≤ Real.log (((2 ^ (t - 2) + 1 : ℕ) : ℝ)) :=
      Real.log_natCast_nonneg (2 ^ (t - 2) + 1)
    nlinarith
  · have hβpos : 0 < (((3 * (16 * (t - 1) + 9) : ℕ) : ℝ)) := by
      have : 0 < 3 * (16 * (t - 1) + 9) := by omega
      exact_mod_cast this
    exact one_div_pos.mpr (mul_pos (by norm_num) hβpos)

end WeightedRIG
