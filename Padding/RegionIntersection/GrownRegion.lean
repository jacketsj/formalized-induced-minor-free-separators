/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.WeightedGraph
import Padding.RegionIntersection.IntersectionModel
import Padding.RegionIntersection.WeightedDist
import Mathlib

/-! # The grown-region auxiliary intersection graph `G^ρ`

Given a region intersection model `μ` of `G` over `H`, vertex weights `w`, and a scale `ρ`,
we form the auxiliary graph `G^ρ` whose vertices are the low-weight vertices
`S = {v | w v ≤ ρ}` and whose region for `x ∈ S` is the *grown region*
`R_x^ρ = ⋃_{y ∈ weightedBall x ρ} μ.region y`.

This graph captures `ρ`-scale closeness of the vertex-weighted metric:
* if `d_w(x,y) < ρ` then `x`,`y` are adjacent in `G^ρ`;
* if `x`,`y` are adjacent in `G^ρ` then `d_w(x,y) ≤ 4ρ`.

These are the forward/backward "claims" of Proposition 4.16 (`prop:weighted-rig-an`) of the
source, specialised to the (endpoint-heavy) metric `weightedDist`.
-/

open SimpleGraph Set

noncomputable section

universe u

variable {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}

/-
Given a `G`-walk `q : u → u'` and points `a ∈ μ.region u`, `c ∈ μ.region u'`, there is an
`H`-walk `a → c` whose vertices each lie in `μ.region v` for some `v` on `q`.
-/
lemma region_walk_chain (μ : RegionIntersectionModel G H) {u u' : V₁} (q : G.Walk u u')
    {a c : V₂} (ha : a ∈ μ.region u) (hc : c ∈ μ.region u') :
    ∃ (p : H.Walk a c), ∀ z ∈ p.support, ∃ v ∈ q.support, z ∈ μ.region v := by
  induction' q with u v q ih generalizing a c;
  · exact ⟨ μ.region_connected u a c ha hc |> Classical.choose, fun z hz => ⟨ u, by simp +decide, μ.region_connected u a c ha hc |> Classical.choose_spec |> fun h => h z hz ⟩ ⟩;
  · obtain ⟨ m, hm ⟩ := μ.adj_intersect v q ‹_›;
    obtain ⟨ p, hp ⟩ := μ.region_connected v a m ha hm.1;
    rename_i h₁ h₂;
    obtain ⟨ q, hq ⟩ := h₂ hm.2 hc;
    refine' ⟨ p.append q, _ ⟩;
    simp +zetaDelta at *;
    rintro z ( hz | hz ) <;> [ exact Or.inl ( hp z hz ) ; exact Or.inr ( hq z hz ) ]

/-- The grown region `R_x^ρ`: union of `μ.region y` over the weighted budget ball of `x`. -/
def grownRegion (μ : RegionIntersectionModel G H) (w : V₁ → ℝ) (ρ : ℝ) (x : V₁) : Set V₂ :=
  ⋃ y ∈ weightedBall G w x ρ, μ.region y

variable {μ : RegionIntersectionModel G H} {w : V₁ → ℝ} {ρ : ℝ}

lemma mem_grownRegion {x y : V₁} {a : V₂} (hy : y ∈ weightedBall G w x ρ)
    (ha : a ∈ μ.region y) : a ∈ grownRegion μ w ρ x := by
  simp only [grownRegion, Set.mem_iUnion]
  exact ⟨y, hy, ha⟩

lemma exists_of_mem_grownRegion {x : V₁} {a : V₂} (ha : a ∈ grownRegion μ w ρ x) :
    ∃ y ∈ weightedBall G w x ρ, a ∈ μ.region y := by
  obtain ⟨y, hy, ha'⟩ := Set.mem_iUnion₂.1 ha
  exact ⟨y, hy, ha'⟩

lemma grownRegion_nonempty (hρ : 0 ≤ ρ) (x : V₁) : (grownRegion μ w ρ x).Nonempty := by
  obtain ⟨a, ha⟩ := μ.region_nonempty x
  exact ⟨a, mem_grownRegion (mem_weightedBall_self hρ x) ha⟩

/-
The grown region is connected in `H`.
-/
lemma grownRegion_connected (hw : ∀ v, 0 ≤ w v) (x : V₁) :
    ∀ a b : V₂, a ∈ grownRegion μ w ρ x → b ∈ grownRegion μ w ρ x →
      ∃ (p : H.Walk a b), ∀ z ∈ p.support, z ∈ grownRegion μ w ρ x := by
  intro a b ha hb
  obtain ⟨ya, hya, ha⟩ := exists_of_mem_grownRegion ha
  obtain ⟨yb, hyb, hb⟩ := exists_of_mem_grownRegion hb
  obtain ⟨qa, hqa⟩ := exists_walk_mem_weightedBall hw hya
  obtain ⟨qb, hqb⟩ := exists_walk_mem_weightedBall hw hyb;
  -- By region_walk_chain μ qa.reverse (a ∈ μ.region ya) (c0 ∈ μ.region x), get H-walk pa : H.Walk a c0; each z ∈ pa.support has v ∈ qa.reverse.support with z ∈ μ.region v, and v ∈ weightedBall G w x ρ, so z ∈ grownRegion μ w ρ x by mem_grownRegion.
  obtain ⟨pa, hpa⟩ : ∃ pa : H.Walk a (Classical.choose (μ.region_nonempty x)), ∀ z ∈ pa.support, ∃ v ∈ qa.support, z ∈ μ.region v := by
    have := region_walk_chain μ qa.reverse ha ( Classical.choose_spec ( μ.region_nonempty x ) ) ; aesop;
  obtain ⟨pb, hpb⟩ : ∃ pb : H.Walk b (Classical.choose (μ.region_nonempty x)), ∀ z ∈ pb.support, ∃ v ∈ qb.support, z ∈ μ.region v := by
    obtain ⟨pb, hpb⟩ : ∃ pb : H.Walk b (Classical.choose (μ.region_nonempty x)), ∀ z ∈ pb.support, ∃ v ∈ (qb.reverse).support, z ∈ μ.region v := by
      apply region_walk_chain μ qb.reverse hb (Classical.choose_spec (μ.region_nonempty x)) |> fun ⟨pb, hpb⟩ => ⟨pb, hpb⟩
    generalize_proofs at *; (
    exact ⟨ pb, fun z hz => by obtain ⟨ v, hv, hv' ⟩ := hpb z hz; exact ⟨ v, by simpa using hv, hv' ⟩ ⟩);
  refine' ⟨ pa.append pb.reverse, _ ⟩;
  simp +zetaDelta at *;
  rintro z ( hz | hz ) <;> [ exact mem_grownRegion ( hqa _ ( hpa _ hz |> Classical.choose_spec |> And.left ) ) ( hpa _ hz |> Classical.choose_spec |> And.right ) ; exact mem_grownRegion ( hqb _ ( hpb _ hz |> Classical.choose_spec |> And.left ) ) ( hpb _ hz |> Classical.choose_spec |> And.right ) ]

/-- The low-weight vertex set `S = {v | w v ≤ ρ}`. -/
def lowWeightSet (w : V₁ → ℝ) (ρ : ℝ) : Set V₁ := {v | w v ≤ ρ}

/-- The grown-region family indexed by the low-weight vertices. -/
def grownRegionFamily (μ : RegionIntersectionModel G H) (w : V₁ → ℝ) (ρ : ℝ) :
    ↥(lowWeightSet w ρ) → Set V₂ := fun x => grownRegion μ w ρ x.1

/-- The auxiliary grown-region intersection graph `G^ρ`. -/
def grownGraph (μ : RegionIntersectionModel G H) (w : V₁ → ℝ) (ρ : ℝ) :
    SimpleGraph ↥(lowWeightSet w ρ) :=
  intersectionGraph (grownRegionFamily μ w ρ)

/-- The canonical region intersection model of `G^ρ` over `H`. -/
def grownModel (hρ : 0 ≤ ρ) (hw : ∀ v, 0 ≤ w v) :
    RegionIntersectionModel (grownGraph μ w ρ) H :=
  intersectionModel H (grownRegionFamily μ w ρ)
    (fun x => grownRegion_nonempty hρ x.1)
    (fun x => grownRegion_connected hw x.1)

@[simp] lemma grownGraph_adj (x y : ↥(lowWeightSet w ρ)) :
    (grownGraph μ w ρ).Adj x y ↔
      x ≠ y ∧ (grownRegion μ w ρ x.1 ∩ grownRegion μ w ρ y.1).Nonempty := Iff.rfl

/-
**Forward claim**: small weighted distance forces adjacency in `G^ρ`.
-/
lemma grownGraph_adj_of_weightedDist_lt (hρ : 0 ≤ ρ)
    (hconn : G.Preconnected) {x y : ↥(lowWeightSet w ρ)} (hxy : x ≠ y)
    (h : G.weightedDist w x.1 y.1 < ρ) :
    (grownGraph μ w ρ).Adj x y := by
  -- By `mem_weightedBall_of_weightedDist_lt`, we have `y.1 ∈ weightedBall G w x.1 ρ`.
  obtain ⟨hy_ball, hy_1⟩ : y.1 ∈ weightedBall G w x.1 ρ ∧ ∃ a ∈ μ.region y.1, a ∈ grownRegion μ w ρ x.1 := by
    refine' ⟨ mem_weightedBall_of_weightedDist_lt (hconn x y) h, _⟩;
    obtain ⟨a, ha⟩ : ∃ a ∈ μ.region y.1, a ∈ grownRegion μ w ρ x.1 := by
      have hy_ball : y.1 ∈ weightedBall G w x.1 ρ := by
        exact mem_weightedBall_of_weightedDist_lt ( hconn x y ) h
      exact ⟨ _, μ.region_nonempty _ |> Classical.choose_spec, mem_grownRegion hy_ball ( μ.region_nonempty _ |> Classical.choose_spec ) ⟩;
    use a;
  exact ⟨ hxy, by rcases hy_1 with ⟨ a, ha₁, ha₂ ⟩ ; exact ⟨ a, ha₂, mem_grownRegion ( mem_weightedBall_self hρ _ ) ha₁ ⟩ ⟩

/-
**Backward claim**: adjacency in `G^ρ` bounds the weighted distance by `4ρ`.
-/
lemma weightedDist_le_of_grownGraph_adj (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected)
    {x y : ↥(lowWeightSet w ρ)} (h : (grownGraph μ w ρ).Adj x y) :
    G.weightedDist w x.1 y.1 ≤ 4 * ρ := by
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ weightedBall G w x.1 ρ, ∃ b ∈ weightedBall G w y.1 ρ, (μ.region a ∩ μ.region b).Nonempty := by
    exact h.2.elim fun z hz => by obtain ⟨ a, ha, ha' ⟩ := exists_of_mem_grownRegion hz.1; obtain ⟨ b, hb, hb' ⟩ := exists_of_mem_grownRegion hz.2; exact ⟨ a, ha, b, hb, ⟨ z, ha', hb' ⟩ ⟩ ;
  -- Bound G.weightedDist w a b ≤ 2ρ.
  have h_dist_ab : G.weightedDist w a b ≤ 2 * ρ := by
    by_cases h : G.Adj a b <;> simp_all +decide [ two_mul ];
    · refine' le_trans ( weightedDist_le_of_adj hw h ) _;
      by_cases ha' : a = x.1 <;> by_cases hb' : b = y.1 <;> simp_all +decide [ lowWeightSet ];
      · exact add_le_add ( x.2 ) ( y.2 );
      · exact add_le_add ( x.2 ) ( weight_le_of_mem_weightedBall hw hb hb' );
      · exact add_le_add ( weight_le_of_mem_weightedBall hw ha ha' ) ( y.2 );
      · exact add_le_add ( weight_le_of_mem_weightedBall hw ha ha' ) ( weight_le_of_mem_weightedBall hw hb hb' );
    · by_cases h : a = b <;> simp_all +decide [ Set.Nonempty ];
      · rw [ SimpleGraph.weightedDist_self ];
        · linarith [ show 0 ≤ ρ by exact le_trans ( hw _ ) x.2 ];
        · exact hw;
      · exact False.elim ( μ.nonadj_disjoint a b h ‹_› |> fun h => h.le_bot ⟨ hab.choose_spec.1, hab.choose_spec.2 ⟩ );
  -- By the triangle inequality, we have G.weightedDist w x.1 y.1 ≤ G.weightedDist w x.1 a + G.weightedDist w a b + G.weightedDist w b y.1.
  have h_triangle : G.weightedDist w x.1 y.1 ≤ G.weightedDist w x.1 a + G.weightedDist w a b + G.weightedDist w b y.1 := by
    exact le_trans ( SimpleGraph.weightedDist_triangle hw hconn _ _ _ ) ( add_le_add ( SimpleGraph.weightedDist_triangle hw hconn _ _ _ ) le_rfl );
  linarith [ weightedDist_le_of_mem_weightedBall hw ha, weightedDist_comm b y.val |> fun h => h ▸ weightedDist_le_of_mem_weightedBall hw hb ]

end