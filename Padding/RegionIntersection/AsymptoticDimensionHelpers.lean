/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.AsymptoticDimension
import Padding.Defs.MuModel

/-! # Helper Lemmas for Region Step

This file contains helper lemmas used in the proof of `region_step`.
-/

open SimpleGraph Set

/-! ## Walk and Distance Lemmas -/

/-- Distance along a walk: the graph distance from the start to the i-th vertex is at most i. -/
lemma dist_getVert_le {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (i : ℕ) : G.dist u (w.getVert i) ≤ i := by
  calc G.dist u (w.getVert i) ≤ (w.take i).length := SimpleGraph.dist_le _
    _ = min i w.length := w.take_length i
    _ ≤ i := Nat.min_le_left i w.length

/-- Distance from the end: the graph distance from the i-th vertex to the end is at most length - i. -/
lemma dist_getVert_end_le {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (i : ℕ) : G.dist (w.getVert i) v ≤ w.length - i := by
  calc G.dist (w.getVert i) v ≤ (w.drop i).length := SimpleGraph.dist_le _
    _ = w.length - i := w.drop_length i

/-- Reachability from walk getVert -/
lemma reachable_of_getVert {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (i : ℕ) : G.Reachable u (w.getVert i) :=
  (w.take i).reachable

/-! ## Gamma-Neighborhood Region Properties -/

/-- The "gamma-neighborhood region" of u: the union of all regions μ(w) for w
reachable from u with graph distance ≤ γ. -/
def gammaNhbdRegion {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (u : V₁) (γ : ℕ) : Set V₂ :=
  ⋃ (w : V₁) (_ : G.Reachable u w ∧ G.dist u w ≤ γ), μ.region w

/-- region(u) ⊆ gammaNhbdRegion μ u γ. -/
lemma region_subset_gammaNhbdRegion_self {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (u : V₁) (γ : ℕ) :
    μ.region u ⊆ gammaNhbdRegion μ u γ := by
  intro x hx
  simp only [gammaNhbdRegion, Set.mem_iUnion]
  exact ⟨u, ⟨⟨.refl _, by simp [SimpleGraph.dist_self]⟩, hx⟩⟩

/-- The gamma-neighborhood region is nonempty. -/
lemma gammaNhbdRegion_nonempty {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (u : V₁) (γ : ℕ) :
    (gammaNhbdRegion μ u γ).Nonempty :=
  ⟨(μ.region_nonempty u).some,
    region_subset_gammaNhbdRegion_self μ u γ (μ.region_nonempty u).some_mem⟩

/-- If G.Reachable u w and dist(u, w) ≤ γ, then region(w) ⊆ gammaNhbdRegion μ u γ. -/
lemma region_subset_gammaNhbdRegion {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (u w : V₁) (γ : ℕ)
    (hr : G.Reachable u w) (hw : G.dist u w ≤ γ) :
    μ.region w ⊆ gammaNhbdRegion μ u γ := fun _ hx =>
  Set.mem_biUnion ⟨hr, hw⟩ hx

/-
If dist(u₁, u₂) ≥ 2γ+2 (with G connected), then vertices in the γ-neighborhoods
are far apart: w₁ ≠ w₂ and they are not G-adjacent.
-/
lemma far_nhbd_not_adj {V₁ : Type*} {G : SimpleGraph V₁}
    (u₁ u₂ w₁ w₂ : V₁) (γ : ℕ)
    (hconn : G.Connected)
    (hdist : 2 * γ + 2 ≤ G.dist u₁ u₂)
    (hw₁ : G.dist u₁ w₁ ≤ γ)
    (hw₂ : G.dist u₂ w₂ ≤ γ) :
    w₁ ≠ w₂ ∧ ¬G.Adj w₁ w₂ := by
  have h_dist : G.dist u₁ u₂ ≤ G.dist u₁ w₁ + G.dist w₁ u₂ := by
    exact Connected.dist_triangle hconn;
  grind +suggestions

/-
If dist(u₁, u₂) ≥ 2γ+2, then the γ-neighborhood regions are disjoint.
-/
lemma gammaNhbdRegion_disjoint {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    (u₁ u₂ : V₁) (γ : ℕ)
    (hconn : G.Connected)
    (hdist : 2 * γ + 2 ≤ G.dist u₁ u₂) :
    Disjoint (gammaNhbdRegion μ u₁ γ) (gammaNhbdRegion μ u₂ γ) := by
  simp +decide [ Set.disjoint_iff_forall_ne, gammaNhbdRegion ];
  intro a x hx₁ hx₂ hx₃ b y hy₁ hy₂ hy₃ hab;
  have := μ.nonadj_disjoint x y;
  grind +suggestions

/-
The union of regions along a G-walk forms an H-connected set.
-/
lemma walk_regions_connected {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    (u v : V₁) (w : G.Walk u v)
    (h₁ h₂ : V₂) (i j : ℕ)
    (hi : i ≤ w.length) (hj : j ≤ w.length)
    (hh₁ : h₁ ∈ μ.region (w.getVert i))
    (hh₂ : h₂ ∈ μ.region (w.getVert j)) :
    ∃ (p : H.Walk h₁ h₂), ∀ x ∈ p.support,
      ∃ k, k ≤ w.length ∧ x ∈ μ.region (w.getVert k) := by
  by_contra h;
  -- Without loss of generality, assume $i \leq j$.
  suffices h_wlog : ∀ (i j : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length) (hij : i ≤ j) (h₁ h₂ : V₂) (hh₁ : h₁ ∈ μ.region (w.getVert i)) (hh₂ : h₂ ∈ μ.region (w.getVert j)), ∃ p : H.Walk h₁ h₂, ∀ x ∈ p.support, ∃ k ≤ w.length, x ∈ μ.region (w.getVert k) by
    by_cases hij : i ≤ j;
    · exact h ( h_wlog i j hi hj hij h₁ h₂ hh₁ hh₂ );
    · exact h ( by obtain ⟨ p, hp ⟩ := h_wlog j i hj hi ( le_of_not_ge hij ) h₂ h₁ hh₂ hh₁; exact ⟨ p.reverse, fun x hx => by simpa using hp x ( by simpa using hx ) ⟩ );
  intro i j hi hj hij h₁ h₂ hh₁ hh₂;
  induction' hij with j hj ih generalizing h₂;
  · obtain ⟨ p, hp ⟩ := μ.region_connected ( w.getVert i ) h₁ h₂ hh₁ hh₂;
    exact ⟨ p, fun x hx => ⟨ i, hj, hp x hx ⟩ ⟩;
  · -- By the adjacency property, there exists a vertex $m$ in the intersection of $\mu(w.getVert j)$ and $\mu(w.getVert (j+1))$.
    obtain ⟨m, hm⟩ : ∃ m, m ∈ μ.region (w.getVert j) ∧ m ∈ μ.region (w.getVert (j + 1)) := by
      have := μ.adj_intersect ( w.getVert j ) ( w.getVert ( j + 1 ) ) ( by
        grind +suggestions );
      exact this;
    obtain ⟨p₁, hp₁⟩ := ih (Nat.le_of_succ_le hj) m hm.left
    obtain ⟨p₂, hp₂⟩ := μ.region_connected (w.getVert (j + 1)) m h₂ hm.right hh₂;
    refine' ⟨ p₁.append p₂, _ ⟩;
    simp +zetaDelta at *;
    rintro x ( hx | hx ) <;> [ exact hp₁ x hx; exact ⟨ j + 1, by linarith, hp₂ x hx ⟩ ]

/-
The gammaNhbdRegion of u is H-connected.
-/
lemma gammaNhbdRegion_connected {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    (u : V₁) (γ : ℕ)
    (a b : V₂) (ha : a ∈ gammaNhbdRegion μ u γ) (hb : b ∈ gammaNhbdRegion μ u γ) :
    ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ gammaNhbdRegion μ u γ := by
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : V₁, G.Reachable u w₁ ∧ G.dist u w₁ ≤ γ ∧ a ∈ μ.region w₁ := by
    unfold gammaNhbdRegion at ha; aesop;
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : V₁, G.Reachable u w₂ ∧ G.dist u w₂ ≤ γ ∧ b ∈ μ.region w₂ := by
    unfold gammaNhbdRegion at hb; aesop;
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : G.Walk u w₁, p₁.length = G.dist u w₁ := by
    have := hw₁.1.exists_walk_length_eq_dist; aesop;
  obtain ⟨p₂, hp₂⟩ : ∃ p₂ : G.Walk u w₂, p₂.length = G.dist u w₂ := by
    have := hw₂.1.exists_walk_length_eq_dist; aesop;
  have h_walk : ∃ p : G.Walk w₁ w₂, ∀ i ≤ p.length, G.dist u (p.getVert i) ≤ γ := by
    use p₁.reverse.append p₂;
    intro i hi; by_cases hi' : i ≤ p₁.length <;> simp_all +decide [ SimpleGraph.Walk.getVert_append ] ;
    · split_ifs <;> simp_all +decide [ SimpleGraph.Walk.getVert_reverse ];
      exact le_trans ( dist_getVert_le _ _ ) ( by omega );
    · have := dist_getVert_le p₂ ( i - G.dist u w₁ ) ; simp_all +decide ;
      grind;
  obtain ⟨p, hp⟩ := h_walk
  obtain ⟨q, hq⟩ : ∃ q : H.Walk a b, ∀ x ∈ q.support, ∃ k, k ≤ p.length ∧ x ∈ μ.region (p.getVert k) := by
    have := walk_regions_connected μ w₁ w₂ p a b 0 p.length ( by simp +decide ) ( by simp +decide ) ?_ ?_ <;> aesop;
  use q;
  intro x hx
  obtain ⟨k, hk₁, hk₂⟩ := hq x hx
  have hk₃ : G.Reachable u (p.getVert k) := by
    exact hw₁.1.trans ( p.take k |> Walk.reachable )
  have hk₄ : G.dist u (p.getVert k) ≤ γ := by
    exact hp k hk₁
  exact Set.mem_iUnion₂.mpr ⟨p.getVert k, ⟨hk₃, hk₄⟩, hk₂⟩

/-
Given an H-walk from set A to set B with A ∩ B = ∅, there exists a vertex in A
on the walk that is H-adjacent to a vertex not in A.
-/
lemma exists_edge_of_walk_disjoint {V : Type*} {H : SimpleGraph V}
    (A B : Set V) (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hdisj : Disjoint A B)
    (p : H.Walk a b) :
    ∃ x y, x ∈ A ∧ H.Adj x y ∧ y ∉ A := by
  induction' p with u v p ih;
  · exact False.elim ( hdisj.le_bot ⟨ ha, hb ⟩ );
  · by_cases hp : p ∈ A <;> simp_all +decide [ Set.disjoint_left ];
    exact ⟨ v, ha, p, by assumption, hp ⟩

/-! ## Reachable-Avoiding Sets -/

/-- The set of vertices reachable from a set A by H-walks that avoid C.
This is the H-connected component of A in V(H) \ C. -/
def reachableAvoiding {V : Type*} (H : SimpleGraph V) (A C : Set V) : Set V :=
  {h | ∃ a ∈ A, ∃ (p : H.Walk a h), ∀ x ∈ p.support, x ∉ C}

lemma reachableAvoiding_supset (H : SimpleGraph V) (A C : Set V) (hdisj : Disjoint A C) :
    A ⊆ reachableAvoiding H A C := by
  intro a ha;
  exact ⟨ a, ha, SimpleGraph.Walk.nil, by simp_all +decide [ Set.disjoint_left ] ⟩

lemma reachableAvoiding_disjoint_right (H : SimpleGraph V) (A C : Set V) :
    Disjoint (reachableAvoiding H A C) C := by
  refine' Set.disjoint_left.mpr _;
  rintro a ⟨ b, hb, p, hp ⟩ ha;
  exact hp a ( by cases p <;> aesop ) ha

lemma reachableAvoiding_connected {V : Type*} {H : SimpleGraph V}
    (A C : Set V) (hdisj : Disjoint A C)
    (hA_conn : ∀ a b : V, a ∈ A → b ∈ A → ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ A)
    (h₁ h₂ : V) (hh₁ : h₁ ∈ reachableAvoiding H A C) (hh₂ : h₂ ∈ reachableAvoiding H A C) :
    ∃ (p : H.Walk h₁ h₂), ∀ x ∈ p.support, x ∈ reachableAvoiding H A C := by
  obtain ⟨ a₁, ha₁, p₁, hp₁ ⟩ := hh₁
  obtain ⟨ a₂, ha₂, p₂, hp₂ ⟩ := hh₂
  have h₃ : ∀ x ∈ p₁.support, x ∈ reachableAvoiding H A C := by
    intro x hx;
    use a₁;
    obtain ⟨ p, hp ⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx;
    obtain ⟨ r, rfl ⟩ := hp;
    exact ⟨ ha₁, p, fun y hy => hp₁ y <| by rw [ SimpleGraph.Walk.support_append ] ; aesop ⟩
  have h₄ : ∀ x ∈ p₂.support, x ∈ reachableAvoiding H A C := by
    intro x hx;
    -- Since x is in the support of p₂, there exists a prefix of p₂ that ends at x.
    obtain ⟨p₃, hp₃⟩ : ∃ p₃ : H.Walk a₂ x, p₃.support ⊆ p₂.support := by
      obtain ⟨ p₃, hp₃ ⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx;
      exact ⟨ p₃, by aesop_cat ⟩;
    exact ⟨ a₂, ha₂, p₃, fun y hy => hp₂ y ( hp₃ hy ) ⟩
  have h₅ : ∃ p : H.Walk a₁ a₂, ∀ x ∈ p.support, x ∈ reachableAvoiding H A C := by
    exact Exists.elim ( hA_conn a₁ a₂ ha₁ ha₂ ) fun p hp => ⟨ p, fun x hx => reachableAvoiding_supset H A C hdisj ( hp x hx ) ⟩
  obtain ⟨ p₃, hp₃ ⟩ := h₅
  use p₁.reverse.append (p₃.append p₂);
  simp +zetaDelta at *;
  rintro x ( hx | hx | hx ) <;> [ exact h₃ x hx; exact hp₃ x hx; exact h₄ x hx ]

/-
If there's an H-walk from a vertex in A to a vertex in C, and A ∩ C = ∅,
then there's an H-edge from reachableAvoiding H A C to C.
-/
lemma reachableAvoiding_adj_of_walk {V : Type*} {H : SimpleGraph V}
    (A C : Set V) (hdisj : Disjoint A C)
    (a c : V) (ha : a ∈ A) (hc : c ∈ C)
    (p : H.Walk a c) :
    ∃ x y, x ∈ reachableAvoiding H A C ∧ y ∈ C ∧ H.Adj x y := by
  have := @exists_edge_of_walk_disjoint;
  specialize this ( reachableAvoiding H A C ) C a c;
  exact H;
  exact this ( reachableAvoiding_supset _ _ _ hdisj ha ) hc ( reachableAvoiding_disjoint_right _ _ _ ) p |> fun ⟨ x, y, hx, hy, hxy ⟩ => ⟨ x, y, hx, by
    contrapose! hxy;
    obtain ⟨ a, ha, p, hp ⟩ := hx;
    exact ⟨ a, ha, p.append ( SimpleGraph.Walk.cons hy SimpleGraph.Walk.nil ), by aesop ⟩, hy ⟩

/-! ## Base Case: No 2-model implies bounded diameter -/

/-
**Key lemma for the base case**: If there is no (μ, S, γ, 2)-model and G is connected,
then all points in S are within distance 2γ+1 of each other.
-/
lemma no_two_model_diam_bound {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    (S : Set V₁) (γ : ℕ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ 2))
    (u v : V₁) (hu : u ∈ S) (hv : v ∈ S) :
    G.dist u v ≤ 2 * γ + 1 := by
  contrapose! hno_model;
  -- Let A = gammaNhbdRegion μ u γ and C = gammaNhbdRegion μ v γ.
  set A := gammaNhbdRegion μ u γ
  set C := gammaNhbdRegion μ v γ;
  -- By reachableAvoiding_adj_of_walk, there exists an H-edge from T₁ to T₂.
  obtain ⟨x, y, hxT₁, hyT₂, hxy⟩ : ∃ x y, x ∈ reachableAvoiding H A C ∧ y ∈ C ∧ H.Adj x y := by
    obtain ⟨a, ha⟩ : ∃ a ∈ A, ∃ b ∈ C, H.Reachable a b := by
      obtain ⟨p, hp⟩ : ∃ p : G.Walk u v, True := by
        have := hconn u v; aesop;
      obtain ⟨a, ha⟩ : ∃ a ∈ μ.region u, ∃ b ∈ μ.region v, H.Reachable a b := by
        have := walk_regions_connected μ u v p;
        obtain ⟨a, ha⟩ : ∃ a, a ∈ μ.region u := by
          exact μ.region_nonempty u
        obtain ⟨b, hb⟩ : ∃ b, b ∈ μ.region v := by
          exact μ.region_nonempty v;
        exact ⟨ a, ha, b, hb, by obtain ⟨ q, hq ⟩ := this a b 0 p.length ( by simp +decide ) ( by simp +decide ) ( by simpa using ha ) ( by simpa using hb ) ; exact ⟨ q ⟩ ⟩;
      exact ⟨ a, region_subset_gammaNhbdRegion_self μ u γ ha.1, ha.2.choose, region_subset_gammaNhbdRegion_self μ v γ ha.2.choose_spec.1, ha.2.choose_spec.2 ⟩;
    obtain ⟨ b, hb, p ⟩ := ha.2;
    apply reachableAvoiding_adj_of_walk;
    exact gammaNhbdRegion_disjoint μ u v γ hconn ( by linarith );
    exacts [ ha.1, hb, p.some ];
  refine' ⟨ ⟨ fun i => if i = 0 then reachableAvoiding H A C else C, _, _, _, _ ⟩, fun i => if i = 0 then u else v, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_two ];
  · exact ⟨ ⟨ x, hxT₁ ⟩, ⟨ y, hyT₂ ⟩ ⟩;
  · refine' ⟨ _, _ ⟩;
    · apply_rules [ reachableAvoiding_connected ];
      · exact gammaNhbdRegion_disjoint μ u v γ hconn ( by linarith );
      · exact fun a b a_1 a_2 => gammaNhbdRegion_connected μ u γ a b a_1 a_2;
    · intro a b ha hb;
      obtain ⟨ p, hp ⟩ := gammaNhbdRegion_connected μ v γ a b ha hb;
      exact ⟨ p, hp ⟩;
  · exact ⟨ reachableAvoiding_disjoint_right _ _ _, Disjoint.symm ( reachableAvoiding_disjoint_right _ _ _ ) ⟩;
  · exact ⟨ ⟨ x, hxT₁, y, hyT₂, hxy ⟩, y, hyT₂, x, hxT₁, hxy.symm ⟩;
  · refine' ⟨ fun w hw hw' => _, fun w hw hw' => _ ⟩;
    · refine' Set.Subset.trans _ ( reachableAvoiding_supset H A C _ );
      · exact region_subset_gammaNhbdRegion μ u w γ hw hw';
      · exact gammaNhbdRegion_disjoint μ u v γ hconn ( by linarith );
    · exact region_subset_gammaNhbdRegion μ v w γ hw hw'

/-
**Base case of region_step** for t = 2.
-/
lemma region_step_base {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H) (S : Set V₁) (γ δ : ℕ)
    (_hγδ : δ ≤ γ) (_hδ : 1 ≤ δ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ 2)) :
    Nonempty (DeltaRhoPartition G δ (2 * γ + 1) S 1) := by
  refine' ⟨ ⟨ fun _ => ⟨ 0, by linarith ⟩, _ ⟩ ⟩;
  intro u v hu hv huv h;
  apply no_two_model_diam_bound μ S γ hconn hno_model u v hu hv

/-! ## Partition Manipulation -/

/-- The radius bound of a `DeltaRhoPartition` may be relaxed upward. -/
def DeltaRhoPartition.mono_rho {V : Type*} {G : SimpleGraph V}
    {δ ρ ρ' : ℕ} {S : Set V} {k : ℕ}
    (P : DeltaRhoPartition G δ ρ S k) (hρ : ρ ≤ ρ') :
    DeltaRhoPartition G δ ρ' S k where
  label := P.label
  component_radius u v hu hv hlabel hchain :=
    le_trans (P.component_radius u v hu hv hlabel hchain) hρ

/-- A DeltaRhoPartition on a subset can be restricted to a smaller subset. -/
def DeltaRhoPartition.restrict {V : Type*} {G : SimpleGraph V}
    {δ ρ : ℕ} {S S' : Set V} {k : ℕ}
    (P : DeltaRhoPartition G δ ρ S k) (hSS : S' ⊆ S) :
    DeltaRhoPartition G δ ρ S' k where
  label := P.label
  component_radius u v hu hv hlabel hchain := by
    apply P.component_radius u v (hSS hu) (hSS hv) hlabel
    exact hchain.mono (fun a b ⟨ha, hb, hla, hlb, hd⟩ => ⟨hSS ha, hSS hb, hla, hlb, hd⟩)

open Classical in
/-- Combine two `DeltaRhoPartition`s on arbitrary sets `S₁`, `S₂` into one partition on
their union by using disjoint label spaces (`Fin k` for `S₁`, the shifted copy for `S₂`).
No separation hypothesis is needed: a δ-chain whose combined label is constant stays
entirely within one of `S₁`, `S₂` (since the label range determines which class a vertex
belongs to), so the radius bound `ρ` is inherited from the corresponding input partition. -/
lemma combine_separated_partitions {V : Type*} {G : SimpleGraph V}
    {δ ρ : ℕ} {S₁ S₂ : Set V} {k : ℕ}
    (P₁ : DeltaRhoPartition G δ ρ S₁ k)
    (P₂ : DeltaRhoPartition G δ ρ S₂ k) :
    Nonempty (DeltaRhoPartition G δ ρ (S₁ ∪ S₂) (2 * k)) := by
  by_contra h_contra;
  obtain ⟨label₁, hlabel₁⟩ : ∃ label₁ : V → Fin k, ∀ u v, u ∈ S₁ → v ∈ S₁ → label₁ u = label₁ v → (Relation.ReflTransGen (fun a b => a ∈ S₁ ∧ b ∈ S₁ ∧ label₁ a = label₁ u ∧ label₁ b = label₁ u ∧ G.dist a b ≤ δ) u v) → G.dist u v ≤ ρ := by
    exact ⟨ P₁.label, P₁.component_radius ⟩;
  obtain ⟨label₂, hlabel₂⟩ : ∃ label₂ : V → Fin k, ∀ u v, u ∈ S₂ → v ∈ S₂ → label₂ u = label₂ v → (Relation.ReflTransGen (fun a b => a ∈ S₂ ∧ b ∈ S₂ ∧ label₂ a = label₂ u ∧ label₂ b = label₂ u ∧ G.dist a b ≤ δ) u v) → G.dist u v ≤ ρ := by
    exact ⟨ P₂.label, P₂.component_radius ⟩;
  refine' h_contra ⟨ fun u => if hu : u ∈ S₁ then ⟨ label₁ u, _ ⟩ else ⟨ label₂ u + k, _ ⟩, _ ⟩ <;> simp_all +decide [ two_mul ];
  exact lt_of_lt_of_le ( Fin.is_lt _ ) ( Nat.le_add_left _ _ );
  intro u v hu hv huv hchain
  by_cases hu₁ : u ∈ S₁
  by_cases hv₁ : v ∈ S₁;
  · apply hlabel₁ u v hu₁ hv₁;
    · grind;
    · convert hchain.mono _ using 1;
      grind;
  · grind +revert;
  · by_cases hv₁ : v ∈ S₁ <;> simp_all +decide [ Fin.ext_iff ];
    · grind +splitImp;
    · convert hlabel₂ u v hu hv huv _ using 1;
      convert hchain.mono _ using 1;
      grind

open Classical in
/-- Combine a pairwise δ-separated family of `DeltaRhoPartition`s (indexed by `ι`) into a
single partition on their union, keeping the **same** number `k` of labels. Separation
(`hsep`) guarantees that no δ-step can join two distinct pieces, so any δ-chain stays
inside one piece and that piece's radius bound `ρ` is inherited. The pieces are
automatically pairwise disjoint, so each vertex of the union lies in a unique piece. -/
lemma combine_indexed_separated {V : Type*} {G : SimpleGraph V}
    {δ ρ : ℕ} {ι : Type*} [Nonempty ι] {pieces : ι → Set V} {k : ℕ}
    (P : ∀ i, DeltaRhoPartition G δ ρ (pieces i) k)
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ pieces i, ∀ v ∈ pieces j, δ < G.dist u v) :
    Nonempty (DeltaRhoPartition G δ ρ (⋃ i, pieces i) k) := by
  by_contra! h_contra;
  -- Define the combined label function L.
  obtain ⟨L, hL⟩ : ∃ L : V → Fin k, ∀ i, ∀ u ∈ pieces i, L u = (P i).label u := by
    have h_unique_piece : ∀ u ∈ ⋃ i, pieces i, ∃! i, u ∈ pieces i := by
      intro u hu; obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp hu; use i; simp_all +decide ;
      intro j hj; specialize hsep j i; contrapose! hsep; aesop;
    choose! f hf₁ hf₂ using h_unique_piece;
    use fun u => if hu : u ∈ ⋃ i, pieces i then (P (f u)).label u else (P (Classical.arbitrary ι)).label u;
    intro i u hu; specialize hf₂ u ( Set.mem_iUnion_of_mem i hu ) i hu; aesop;
  refine' h_contra.elim ⟨ L, _ ⟩;
  intro u v hu hv huv hchain
  obtain ⟨i, hi⟩ : ∃ i, u ∈ pieces i := by
    exact Set.mem_iUnion.mp hu
  obtain ⟨j, hj⟩ : ∃ j, v ∈ pieces j := by
    exact Set.mem_iUnion.mp hv
  have h_eq : i = j := by
    have h_dist : ∀ x y, Relation.ReflTransGen (fun a b => a ∈ ⋃ i, pieces i ∧ b ∈ ⋃ i, pieces i ∧ L a = L u ∧ L b = L u ∧ G.dist a b ≤ δ) x y → ∀ i, x ∈ pieces i → ∀ j, y ∈ pieces j → i = j := by
      intro x y hchain i hi j hj
      induction' hchain with x y hchain ih generalizing i j
      all_goals generalize_proofs at *;
      · exact Classical.not_not.1 fun h => by have := hsep i j h x hi x hj; linarith [ show G.dist x x = 0 from by simp +decide [ SimpleGraph.dist_self ] ] ;
      · obtain ⟨ k, hk ⟩ := Set.mem_iUnion.mp ih.1
        generalize_proofs at *;
        grind +splitImp
    generalize_proofs at *;
    exact h_dist u v hchain i hi j hj
  subst h_eq
  exact (P i).component_radius u v hi hj (by
  rw [ ← hL i u hi, ← hL i v hj, huv ]) (by
  have hchain_i : ∀ {a b : V}, Relation.ReflTransGen (fun a b => a ∈ ⋃ i, pieces i ∧ b ∈ ⋃ i, pieces i ∧ L a = L u ∧ L b = L u ∧ G.dist a b ≤ δ) a b → a ∈ pieces i → b ∈ pieces i → Relation.ReflTransGen (fun a b => a ∈ pieces i ∧ b ∈ pieces i ∧ (P i).label a = (P i).label u ∧ (P i).label b = (P i).label u ∧ G.dist a b ≤ δ) a b := by
    intros a b hab ha hb
    induction' hab with a b hab ih;
    · exact .refl;
    · obtain ⟨j, hj⟩ : ∃ j, a ∈ pieces j := by
        exact Set.mem_iUnion.mp ih.1;
      grind +extAll;
  exact hchain_i hchain hi hj)