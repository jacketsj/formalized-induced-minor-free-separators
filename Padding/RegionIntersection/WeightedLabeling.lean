/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.RegionIntersection.GrownRegion
import Padding.RegionIntersection.AsymptoticDimension
import Padding.RegionIntersection.InduceComponent
import Mathlib

/-! # The combined labeling of the grown-region graph

For a region intersection model `μ` of `G` over a `Kₜ`-minor-free host `H`, fixed weights
`w` and scale `ρ`, we label the low-weight vertices `S` of the grown graph `G^ρ` by applying
the unweighted asymptotic-dimension partition to each connected component of `G^ρ`.

The two key consequences (in the vertex-weighted metric `d_w`) are:

* **separation** (`combined_separation`): two equally-labelled vertices that are *not*
  connected by a same-label adjacency chain in `G^ρ` are at `d_w`-distance at least `ρ`;
* **diameter** (`combined_diam`): two vertices connected by a same-label adjacency chain are
  at `d_w`-distance at most `(4(t-1)+2)·4ρ`.

These are the two halves needed to turn the components of the labelling into a sparse cover.
-/

open SimpleGraph BandPartition Set

noncomputable section

universe u

namespace WeightedRIG

variable {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
  {μ : RegionIntersectionModel G H} {t : ℕ} {w : V₁ → ℝ} {ρ : ℝ}

/-- The per-component `(1, 4(t-1)+2)`-partition of `G^ρ` obtained from the unweighted
asymptotic-dimension theorem applied to each connected component. -/
def compPart (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ)
    (c : (grownGraph μ w ρ).ConnectedComponent) :
    DeltaRhoPartition ((grownGraph μ w ρ).induce c.supp) 1 (4 * (t - 1) * 1 + 2) Set.univ
      (2 ^ (t - 2)) :=
  Classical.choice
    (region_intersection_asymptotic_dimension (induceModel (grownModel hρ hw) c.supp) t ht hH 1
      le_rfl (connectedComponent_induce_connected c))

/-- The combined label of a low-weight vertex `x`: the label assigned to `x` by the partition
of its own connected component. -/
def lbl (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ)
    (x : ↥(lowWeightSet w ρ)) : Fin (2 ^ (t - 2)) :=
  (compPart μ t ht hH hw hρ ((grownGraph μ w ρ).connectedComponentMk x)).label
    ⟨x, (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl⟩

variable (ht : 2 ≤ t) (hH : H.ExcludesMinor t) (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ)

/-- The single-step relation: equal label and adjacency in `G^ρ`. -/
def compStep (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) (a b : ↥(lowWeightSet w ρ)) : Prop :=
  lbl μ t ht hH hw hρ a = lbl μ t ht hH hw hρ b ∧ (grownGraph μ w ρ).Adj a b

/-- The component relation: connected by a same-label adjacency chain in `G^ρ`. -/
def compRel (μ : RegionIntersectionModel G H) (t : ℕ) (ht : 2 ≤ t) (hH : H.ExcludesMinor t)
    (hw : ∀ v, 0 ≤ w v) (hρ : 0 ≤ ρ) (a b : ↥(lowWeightSet w ρ)) : Prop :=
  Relation.ReflTransGen (compStep μ t ht hH hw hρ) a b

lemma compStep_symm {a b : ↥(lowWeightSet w ρ)}
    (h : compStep μ t ht hH hw hρ a b) : compStep μ t ht hH hw hρ b a :=
  ⟨h.1.symm, h.2.symm⟩

lemma compRel_symm {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) : compRel μ t ht hH hw hρ b a :=
  Relation.ReflTransGen.symmetric (fun _ _ => compStep_symm ht hH hw hρ) h

/-
Equal-label vertices not in the same component-chain are `ρ`-far in `d_w`.
-/
lemma combined_separation (hconn : G.Preconnected) {a b : ↥(lowWeightSet w ρ)}
    (hlab : lbl μ t ht hH hw hρ a = lbl μ t ht hH hw hρ b)
    (hnr : ¬ compRel μ t ht hH hw hρ a b) :
    ρ ≤ G.weightedDist w a.1 b.1 := by
  contrapose! hnr;
  by_cases hab : a = b;
  · exact hab ▸ Relation.ReflTransGen.refl;
  · exact .single ⟨ hlab, grownGraph_adj_of_weightedDist_lt hρ hconn hab hnr ⟩

/-- A `G^ρ`-walk of length `n` bounds the weighted distance of its endpoints by `n·4ρ`. -/
lemma dw_le_length_mul (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected) {a b : ↥(lowWeightSet w ρ)}
    (p : (grownGraph μ w ρ).Walk a b) :
    G.weightedDist w a.1 b.1 ≤ p.length * (4 * ρ) := by
  induction p with
  | nil => simp [SimpleGraph.weightedDist_self hw]
  | @cons u v b'' h q ih =>
    have htri := SimpleGraph.weightedDist_triangle hw hconn u.1 v.1 b''.1
    have hstep := weightedDist_le_of_grownGraph_adj hw hconn h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

/-
A same-label component-chain gives equal labels at the endpoints.
-/
lemma compRel_label_eq {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) :
    lbl μ t ht hH hw hρ a = lbl μ t ht hH hw hρ b := by
  induction h; aesop;
  cases ‹compStep μ t ht hH hw hρ _ _› ; aesop

/-
A component-chain witnesses reachability in `G^ρ`.
-/
lemma compRel_reachable {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) : (grownGraph μ w ρ).Reachable a b := by
  have h_compRel : ∀ a b : ↥(lowWeightSet w ρ), compStep μ t ht hH hw hρ a b → (grownGraph μ w ρ).Reachable a b := by
    exact fun a b h => SimpleGraph.Adj.reachable h.2;
  induction h;
  · exact SimpleGraph.Reachable.refl _;
  · exact SimpleGraph.Reachable.trans ‹_› ( h_compRel _ _ ‹_› )

/-
A component-chain stays inside one connected component.
-/
lemma compRel_component_eq {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) :
    (grownGraph μ w ρ).connectedComponentMk a = (grownGraph μ w ρ).connectedComponentMk b := by
  convert SimpleGraph.ConnectedComponent.eq.mpr _;
  exact compRel_reachable ht hH hw hρ h

/-
The combined label of `x` equals the label given by the partition of any component
containing `x`.
-/
lemma lbl_spec (c : (grownGraph μ w ρ).ConnectedComponent) (x : ↥(lowWeightSet w ρ))
    (hx : x ∈ c.supp) :
    lbl μ t ht hH hw hρ x = (compPart μ t ht hH hw hρ c).label ⟨x, hx⟩ := by
  convert rfl;
  congr;
  all_goals simp_all +decide [ SimpleGraph.ConnectedComponent.mem_supp_iff ]

/-
The component-chain, lifted to the induced subgraph on the connected component of `a`,
is a chain of the partition's `δ`-step relation.
-/
lemma compRel_induce_chain {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b)
    (ha : a ∈ ((grownGraph μ w ρ).connectedComponentMk a).supp)
    (hb : b ∈ ((grownGraph μ w ρ).connectedComponentMk a).supp) :
    Relation.ReflTransGen
      (fun x y : ↥(((grownGraph μ w ρ).connectedComponentMk a).supp) =>
        x ∈ (Set.univ : Set ↥(((grownGraph μ w ρ).connectedComponentMk a).supp)) ∧
        y ∈ (Set.univ : Set ↥(((grownGraph μ w ρ).connectedComponentMk a).supp)) ∧
        (compPart μ t ht hH hw hρ ((grownGraph μ w ρ).connectedComponentMk a)).label x =
          (compPart μ t ht hH hw hρ ((grownGraph μ w ρ).connectedComponentMk a)).label ⟨a, ha⟩ ∧
        (compPart μ t ht hH hw hρ ((grownGraph μ w ρ).connectedComponentMk a)).label y =
          (compPart μ t ht hH hw hρ ((grownGraph μ w ρ).connectedComponentMk a)).label ⟨a, ha⟩ ∧
        ((grownGraph μ w ρ).induce ((grownGraph μ w ρ).connectedComponentMk a).supp).dist x y ≤ 1)
      ⟨a, ha⟩ ⟨b, hb⟩ := by
  revert hb;
  induction h;
  · exact fun _ => Relation.ReflTransGen.refl;
  · rename_i b c hb hc ih;
    intro hc'
    have hb' : b ∈ ((grownGraph μ w ρ).connectedComponentMk a).supp := by
      have := compRel_component_eq ht hH hw hρ hb; simp_all +decide [ SimpleGraph.ConnectedComponent.mem_supp_iff ] ;
      exact this.symm;
    refine' ih hb' |> fun h => h.tail _;
    refine' ⟨ Set.mem_univ _, Set.mem_univ _, _, _, _ ⟩;
    · lia;
    · have := compRel_label_eq ht hH hw hρ ( hb.tail hc );
      grind +suggestions;
    · refine' le_trans ( SimpleGraph.dist_le _ ) _;
      exact SimpleGraph.Walk.cons ( by simpa using hc.2 ) SimpleGraph.Walk.nil;
      simp +decide

/-- **Component radius (combined).** Two equally-labelled vertices connected by a same-label
adjacency chain are at `G^ρ`-graph-distance at most `4(t-1)+2`. -/
lemma combined_component_radius {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) :
    (grownGraph μ w ρ).dist a b ≤ 4 * (t - 1) * 1 + 2 := by
  set Gρ := grownGraph μ w ρ with hGρ
  set c := Gρ.connectedComponentMk a with hc
  have ha : a ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  have hb : b ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (compRel_component_eq ht hH hw hρ h).symm
  rw [← induce_dist_eq_supp c ⟨a, ha⟩ ⟨b, hb⟩]
  refine (compPart μ t ht hH hw hρ c).component_radius ⟨a, ha⟩ ⟨b, hb⟩ (Set.mem_univ _)
    (Set.mem_univ _) ?_ (compRel_induce_chain ht hH hw hρ h ha hb)
  rw [← lbl_spec ht hH hw hρ c a ha, ← lbl_spec ht hH hw hρ c b hb]
  exact compRel_label_eq ht hH hw hρ h

/-
**Diameter (combined).** Two vertices connected by a same-label adjacency chain are at
`d_w`-distance at most `(4(t-1)+2)·4ρ`.
-/
lemma combined_diam (hconn : G.Preconnected) {a b : ↥(lowWeightSet w ρ)}
    (h : compRel μ t ht hH hw hρ a b) :
    G.weightedDist w a.1 b.1 ≤ (4 * (t - 1) * 1 + 2 : ℕ) * (4 * ρ) := by
  obtain ⟨ p, hp ⟩ := ( compRel_reachable ht hH hw hρ h ).exists_walk_length_eq_dist;
  have := combined_component_radius ht hH hw hρ h;
  exact le_trans ( dw_le_length_mul hw hconn p ) ( mul_le_mul_of_nonneg_right ( mod_cast hp ▸ this ) ( by positivity ) )

end WeightedRIG