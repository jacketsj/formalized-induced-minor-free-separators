/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.MuModel
import Padding.Defs.AsymptoticDimension
import Padding.RegionIntersection.AsymptoticDimensionHelpers
import Padding.RegionIntersection.IntersectionModel

/-! # The auxiliary intersection graph for a single BFS band

This file carries out the construction underlying `RegionStepInductive.band_partition`:
the auxiliary intersection graph `G'_{i-γ, i+γ+δ}` of the BBEGPS region-step proof, the
model-extension argument, and the `G' ↔ G` distance transfer.

Throughout, `D v = G.dist xstar v` is the BFS distance from a fixed root `xstar`, and
`i` is a fixed layer index (in the application `i = 2γ+1+kδ`, so the band is
`{v | i+1 ≤ D v ≤ i+δ}`).

To make the auxiliary model's bags automatically disjoint from the low-layer region
`C = μ(V_{0,i-γ-1})`, the *auxiliary host* is `H` with edges restricted to `Cᶜ`
(`restrictHost`).  Any `restrictHost`-connected set that meets `Cᶜ` is contained in `Cᶜ`.
-/

open SimpleGraph Set

namespace BandPartition

universe u

variable {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}

/-! ## Host restricted to the complement of a set -/

/-- `restrictHost H C` is `H` with edges kept only between vertices outside `C`. -/
def restrictHost (H : SimpleGraph V₂) (C : Set V₂) : SimpleGraph V₂ where
  Adj a b := H.Adj a b ∧ a ∉ C ∧ b ∉ C
  symm := by rintro a b ⟨hab, ha, hb⟩; exact ⟨hab.symm, hb, ha⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

lemma restrictHost_le (H : SimpleGraph V₂) (C : Set V₂) : restrictHost H C ≤ H :=
  fun _ _ h => h.1

lemma restrictHost_adj_notMem {H : SimpleGraph V₂} {C : Set V₂} {a b : V₂}
    (h : (restrictHost H C).Adj a b) : a ∉ C ∧ b ∉ C := ⟨h.2.1, h.2.2⟩

/-- An `H`-walk all of whose vertices avoid `C` is a `restrictHost H C`-walk. -/
lemma walk_to_restrictHost {H : SimpleGraph V₂} {C : Set V₂} {a b : V₂}
    (p : H.Walk a b) (hp : ∀ x ∈ p.support, x ∉ C) :
    ∃ (q : (restrictHost H C).Walk a b), ∀ x ∈ q.support, x ∈ p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | cons hadj p ih =>
    rename_i a c b
    have hsub : ∀ x ∈ p.support, x ∉ C := fun x hx => hp x (by simp [hx])
    obtain ⟨q, hq⟩ := ih hsub
    refine ⟨SimpleGraph.Walk.cons ⟨hadj, hp a (by simp), hp c (by simp)⟩ q, ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (hq x hx)

/-! ## Connected component of a vertex inside a set -/

/-- `compIn H Sset a` is the set of vertices reachable from `a` by `H`-walks staying inside
`Sset` — i.e. the connected component of `a` in the induced subgraph `H[Sset]`. -/
def compIn (H : SimpleGraph V₂) (Sset : Set V₂) (a : V₂) : Set V₂ :=
  {b | ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ Sset}

lemma compIn_self (H : SimpleGraph V₂) {Sset : Set V₂} {a : V₂} (ha : a ∈ Sset) :
    a ∈ compIn H Sset a :=
  ⟨SimpleGraph.Walk.nil, by simpa using ha⟩

lemma compIn_subset (H : SimpleGraph V₂) (Sset : Set V₂) (a : V₂) :
    compIn H Sset a ⊆ Sset := by
  rintro b ⟨p, hp⟩
  exact hp b (by cases p <;> simp)

/-- `compIn H Sset a` is `H`-connected: any two of its points are joined by an `H`-walk that
stays inside the component. -/
lemma compIn_connected (H : SimpleGraph V₂) (Sset : Set V₂) (a : V₂)
    (b c : V₂) (hb : b ∈ compIn H Sset a) (hc : c ∈ compIn H Sset a) :
    ∃ (p : H.Walk b c), ∀ x ∈ p.support, x ∈ compIn H Sset a := by
  obtain ⟨pb, hpb⟩ := hb
  obtain ⟨pc, hpc⟩ := hc
  refine ⟨pb.reverse.append pc, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_append] at hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx
    exact ⟨q, fun y hy => hpb y (by rw [hqr, SimpleGraph.Walk.support_append]; exact List.mem_append_left _ hy)⟩
  · have hx' : x ∈ pc.support := List.mem_of_mem_tail hx
    obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx'
    exact ⟨q, fun y hy => hpc y (by rw [hqr, SimpleGraph.Walk.support_append]; exact List.mem_append_left _ hy)⟩

/-! ## The auxiliary intersection graph `G'_{i-γ, i+γ+δ}` -/

section Aux

variable (μ : RegionIntersectionModel G H) (xstar : V₁) (i γ δ : ℕ)

/-- The low-layer region `C = μ(V_{0, i-γ-1})`: the union of regions of vertices within BFS
distance `i-γ-1` of the root. -/
def lowRegion : Set V₂ :=
  ⋃ (v : V₁) (_ : G.dist xstar v ≤ i - γ - 1), μ.region v

/-- The auxiliary host: `H` with edges restricted to `(lowRegion)ᶜ`. -/
def auxHost : SimpleGraph V₂ := restrictHost H (lowRegion μ xstar i γ)

/-- Boundary index type: pairs `(v, a)` where `v` is on BFS layer `i-γ` and `a` is a point of
`μ(v)` outside the low region.  Such a pair names the connected component of `a` in
`H[μ(v) \ C]`. -/
abbrev BdryIdx : Type u :=
  {p : V₁ × V₂ // G.dist xstar p.1 = i - γ ∧ p.2 ∈ μ.region p.1 ∧ p.2 ∉ lowRegion μ xstar i γ}

/-- Band index type: vertices in BFS layers `[i-γ+1, i+γ+δ]`. -/
abbrev BandIdx (G : SimpleGraph V₁) (xstar : V₁) (i γ δ : ℕ) : Type u :=
  {u : V₁ // i - γ + 1 ≤ G.dist xstar u ∧ G.dist xstar u ≤ i + γ + δ}

/-- The auxiliary vertex type `W = V'_{i-γ} ⊔ V_{i-γ+1, i+γ+δ}`. -/
abbrev AuxV : Type u := BdryIdx μ xstar i γ ⊕ BandIdx G xstar i γ δ

/-- The auxiliary region family: a boundary vertex maps to its component (in the auxiliary
host) of `μ(v) \ C`, a band vertex `u` maps to `μ(u)`. -/
abbrev auxRegion : AuxV μ xstar i γ δ → Set V₂ :=
  Sum.elim
    (fun p : BdryIdx μ xstar i γ =>
      compIn (auxHost μ xstar i γ) (μ.region p.val.1 \ lowRegion μ xstar i γ) p.val.2)
    (fun u : BandIdx G xstar i γ δ => μ.region u.val)

/-
For a band vertex `u` (BFS distance `≥ i-γ+1`), its region `μ(u)` is disjoint from the low
region `C` (BFS distance `≤ i-γ-1`), by the BFS 1-Lipschitz property.
-/
lemma band_region_disjoint (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i)
    (u : V₁) (hu : i - γ + 1 ≤ G.dist xstar u) :
    μ.region u ∩ lowRegion μ xstar i γ = ∅ := by
  by_contra h_nonempty;
  obtain ⟨ v, hv ⟩ := Set.nonempty_iff_ne_empty.mpr h_nonempty;
  obtain ⟨ w, hw ⟩ := Set.mem_iUnion₂.mp hv.2;
  -- By the region model property, either $u = w$ or $G.Adj u w$.
  by_cases h_adj : u = w ∨ G.Adj u w;
  · grind +suggestions;
  · exact μ.nonadj_disjoint u w ( by tauto ) ( by tauto ) |> fun h => h.le_bot ⟨ hv.1, hw.2 ⟩

lemma auxRegion_nonempty (w : AuxV μ xstar i γ δ) :
    (auxRegion μ xstar i γ δ w).Nonempty := by
  rcases w with p | u
  · exact ⟨p.val.2, compIn_self _ ⟨p.property.2.1, p.property.2.2⟩⟩
  · exact μ.region_nonempty u.val

lemma auxRegion_connected (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i)
    (w : AuxV μ xstar i γ δ) (a b : V₂)
    (ha : a ∈ auxRegion μ xstar i γ δ w) (hb : b ∈ auxRegion μ xstar i γ δ w) :
    ∃ (p : (auxHost μ xstar i γ).Walk a b), ∀ x ∈ p.support, x ∈ auxRegion μ xstar i γ δ w := by
  rcases w with p | u
  · exact compIn_connected (auxHost μ xstar i γ) (μ.region p.val.1 \ lowRegion μ xstar i γ)
      p.val.2 a b ha hb
  · -- `μ(u)` is connected in `H` via walks inside `μ(u) ⊆ Cᶜ`, hence connected in `auxHost`.
    obtain ⟨q, hq⟩ := μ.region_connected u.val a b ha hb
    have hdisj := band_region_disjoint μ xstar i γ hconn hi u.val u.property.1
    have hsub : ∀ x ∈ q.support, x ∉ lowRegion μ xstar i γ := by
      intro x hx hxC
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj x) ⟨hq x hx, hxC⟩
    obtain ⟨r, hr⟩ := walk_to_restrictHost q hsub
    exact ⟨r, fun x hx => hq x (hr x hx)⟩

/-- The auxiliary graph `G' = intersectionGraph (auxRegion …)`. -/
def auxGraph : SimpleGraph (AuxV μ xstar i γ δ) := intersectionGraph (auxRegion μ xstar i γ δ)

/-- The auxiliary region intersection model of `G'` over the auxiliary host. -/
def auxModel (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) :
    RegionIntersectionModel (auxGraph μ xstar i γ δ) (auxHost μ xstar i γ) :=
  intersectionModel (auxHost μ xstar i γ) (auxRegion μ xstar i γ δ)
    (auxRegion_nonempty μ xstar i γ δ)
    (auxRegion_connected μ xstar i γ δ hconn hi)

/-! ## Projection back to `G` and the distance transfer -/

/-- The projection `W → V₁`: a boundary vertex `(v, a)` maps to `v`, a band vertex `u` to `u`. -/
def auxProj : AuxV μ xstar i γ δ → V₁ :=
  Sum.elim (fun p : BdryIdx μ xstar i γ => p.val.1) (fun u : BandIdx G xstar i γ δ => u.val)

@[simp] lemma auxProj_inr (u : BandIdx G xstar i γ δ) :
    auxProj μ xstar i γ δ (Sum.inr u) = u.val := rfl

/-- Every auxiliary region is contained in the `μ`-region of its projection. -/
lemma auxRegion_subset_proj (w : AuxV μ xstar i γ δ) :
    auxRegion μ xstar i γ δ w ⊆ μ.region (auxProj μ xstar i γ δ w) := by
  rcases w with p | u
  · exact fun x hx => (compIn_subset _ _ _ hx).1
  · exact fun x hx => hx

/-- An edge of the auxiliary graph projects to an edge of `G` or to a single vertex. -/
lemma auxProj_adj_or_eq {w₁ w₂ : AuxV μ xstar i γ δ}
    (h : (auxGraph μ xstar i γ δ).Adj w₁ w₂) :
    auxProj μ xstar i γ δ w₁ = auxProj μ xstar i γ δ w₂ ∨
      G.Adj (auxProj μ xstar i γ δ w₁) (auxProj μ xstar i γ δ w₂) := by
  obtain ⟨hne, x, hx⟩ := h
  have hx1 : x ∈ μ.region (auxProj μ xstar i γ δ w₁) := auxRegion_subset_proj μ xstar i γ δ w₁ hx.1
  have hx2 : x ∈ μ.region (auxProj μ xstar i γ δ w₂) := auxRegion_subset_proj μ xstar i γ δ w₂ hx.2
  by_cases heq : auxProj μ xstar i γ δ w₁ = auxProj μ xstar i γ δ w₂
  · exact Or.inl heq
  · refine Or.inr ?_
    by_contra hadj
    exact (μ.nonadj_disjoint _ _ heq hadj).le_bot ⟨hx1, hx2⟩

/-
**Distance transfer (`G' → G`)**: a walk in the auxiliary graph projects to a `G`-walk of
no greater length, so `G.dist` between projections is `≤` the auxiliary-graph distance.
-/
lemma dist_proj_le (_hconn : G.Connected) (w₁ w₂ : AuxV μ xstar i γ δ)
    (hr : (auxGraph μ xstar i γ δ).Reachable w₁ w₂) :
    G.dist (auxProj μ xstar i γ δ w₁) (auxProj μ xstar i γ δ w₂)
      ≤ (auxGraph μ xstar i γ δ).dist w₁ w₂ := by
  obtain ⟨ p, hp ⟩ := hr.exists_walk_length_eq_dist;
  -- By induction on the length of the walk p, we can show that there exists a walk q in G from auxProj w₁ to auxProj w₂ with length at most p.length.
  have h_ind : ∀ w₁ w₂ : AuxV μ xstar i γ δ, ∀ p : (auxGraph μ xstar i γ δ).Walk w₁ w₂, ∃ q : G.Walk (auxProj μ xstar i γ δ w₁) (auxProj μ xstar i γ δ w₂), q.length ≤ p.length := by
    intro w₁ w₂ p
    induction' p with w₁ w₂ p ih;
    · exact ⟨ SimpleGraph.Walk.nil, by simp +decide ⟩;
    · rename_i h₁ h₂ h₃;
      obtain ⟨ q, hq ⟩ := h₃;
      by_cases h : auxProj μ xstar i γ δ w₂ = auxProj μ xstar i γ δ p;
      · exact ⟨ q.copy ( by aesop ) ( by aesop ), by simpa using hq.trans ( by simp +decide ) ⟩;
      · have := auxProj_adj_or_eq μ xstar i γ δ h₁; simp_all +decide ;
        exact ⟨ SimpleGraph.Walk.cons this q, by simp +arith +decide; linarith ⟩;
  exact hp ▸ by obtain ⟨ q, hq ⟩ := h_ind w₁ w₂ p; exact le_trans ( SimpleGraph.dist_le q ) hq;

/-
**Distance transfer (`G → G'`)**: a single `G`-step of length `≤ δ` between band vertices
lifts to an auxiliary-graph step of length `≤ δ`.  The shortest `G`-path of length `≤ δ` stays
in BFS layers `[i-γ+1, i+γ+δ]` (using `δ ≤ γ`), so all its vertices are band vertices and
consecutive ones are auxiliary-graph adjacent.
-/
lemma step_lift (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (hγδ : δ ≤ γ)
    (u v : BandIdx G xstar i γ δ)
    (hu1 : i + 1 ≤ G.dist xstar u.val) (hu2 : G.dist xstar u.val ≤ i + δ)
    (hv1 : i + 1 ≤ G.dist xstar v.val) (hv2 : G.dist xstar v.val ≤ i + δ)
    (hd : G.dist u.val v.val ≤ δ) :
    (auxGraph μ xstar i γ δ).dist (Sum.inr u) (Sum.inr v) ≤ δ := by
  obtain ⟨p, hp⟩ : ∃ p : G.Walk u.val v.val, p.length = G.dist u.val v.val ∧ ∀ x ∈ p.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ := by
    have := hconn.exists_walk_length_eq_dist u.val v.val;
    obtain ⟨ p, hp ⟩ := this; use p; simp_all +decide [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] ;
    intro x j hx hj; have := dist_getVert_le p j; have := dist_getVert_end_le p j; simp_all +decide [ SimpleGraph.dist_comm ] ;
    have h_triangle : G.dist xstar x ≤ G.dist xstar u.val + G.dist u.val x ∧ G.dist xstar u.val ≤ G.dist xstar x + G.dist x u.val := by
      have h_triangle : ∀ (a b c : V₁), G.Reachable a b → G.Reachable b c → G.dist a c ≤ G.dist a b + G.dist b c := by
        intros a b c hab hbc;
        obtain ⟨ p, hp ⟩ := hab.exists_walk_length_eq_dist
        obtain ⟨ q, hq ⟩ := hbc.exists_walk_length_eq_dist
        have h_walk : ∃ r : G.Walk a c, r.length ≤ p.length + q.length := by
          exact ⟨ p.append q, by simp +decide ⟩;
        exact le_trans ( SimpleGraph.dist_le _ ) ( by linarith [ h_walk.choose_spec ] );
      exact ⟨ h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ), h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ) ⟩;
    grind +suggestions;
  have h_lift : ∀ {a b : V₁} (q : G.Walk a b) (hq : ∀ x ∈ q.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ), ∃ p' : (auxGraph μ xstar i γ δ).Walk (Sum.inr ⟨a, by
    exact hq a ( by simp +decide )⟩) (Sum.inr ⟨b, by
    exact hq b ( by simp )⟩), p'.length ≤ q.length := by
    intro a b q hq; induction' q with a b q ih <;> simp_all +decide ;
    all_goals generalize_proofs at *;
    rename_i h₁ h₂ h₃;
    obtain ⟨ p', hp' ⟩ := h₂;
    refine' ⟨ SimpleGraph.Walk.cons _ p', _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.length_cons ];
    exact ⟨ by aesop, μ.adj_intersect _ _ ‹_› ⟩
  generalize_proofs at *;
  obtain ⟨ p', hp' ⟩ := h_lift p hp.2; exact le_trans ( SimpleGraph.dist_le p' ) ( by linarith ) ;

/-- The low region equals the `(i-γ-1)`-neighbourhood region of the root (for connected `G`). -/
lemma lowRegion_eq_gammaNhbd (hconn : G.Connected) :
    lowRegion μ xstar i γ = gammaNhbdRegion μ xstar (i - γ - 1) := by
  ext x
  simp only [lowRegion, gammaNhbdRegion, Set.mem_iUnion]
  constructor
  · rintro ⟨v, hv, hx⟩; exact ⟨v, ⟨hconn _ _, hv⟩, hx⟩
  · rintro ⟨v, ⟨_, hv⟩, hx⟩; exact ⟨v, hv, hx⟩

/-- The low region is nonempty. -/
lemma lowRegion_nonempty (hconn : G.Connected) :
    (lowRegion μ xstar i γ).Nonempty := by
  rw [lowRegion_eq_gammaNhbd μ xstar i γ hconn]; exact gammaNhbdRegion_nonempty μ xstar _

/-- The low region is `H`-connected. -/
lemma lowRegion_connected (hconn : G.Connected) (a b : V₂)
    (ha : a ∈ lowRegion μ xstar i γ) (hb : b ∈ lowRegion μ xstar i γ) :
    ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ lowRegion μ xstar i γ := by
  rw [lowRegion_eq_gammaNhbd μ xstar i γ hconn] at *
  exact gammaNhbdRegion_connected μ xstar _ a b ha hb

/-- A `restrictHost H C`-walk starting outside `C` stays outside `C`. -/
lemma restrictHost_support_notMem {C : Set V₂} {a b : V₂}
    (p : (restrictHost H C).Walk a b) (ha : a ∉ C) : ∀ x ∈ p.support, x ∉ C := by
  induction p with
  | nil => simpa using ha
  | cons hadj p ih =>
    intro x hx
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih (restrictHost_adj_notMem hadj).2 x hx

/-
**General band-walk lift**: a `G`-walk of length `≤ γ` between band vertices, all of whose
intermediate vertices lie in BFS layers `[i-γ+1, i+γ+δ]`, lifts to an auxiliary-graph walk
of no greater length.  Used with the geodesic between two band vertices.
-/
lemma band_walk_lift (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (hγδ : δ ≤ γ)
    (u v : BandIdx G xstar i γ δ)
    (hu1 : i + 1 ≤ G.dist xstar u.val) (hu2 : G.dist xstar u.val ≤ i + δ)
    (hv1 : i + 1 ≤ G.dist xstar v.val) (hv2 : G.dist xstar v.val ≤ i + δ)
    (hd : G.dist u.val v.val ≤ γ) :
    ∃ p : (auxGraph μ xstar i γ δ).Walk (Sum.inr u) (Sum.inr v),
      p.length ≤ G.dist u.val v.val := by
  by_contra h_contra;
  obtain ⟨ p, hp ⟩ := hconn.exists_walk_length_eq_dist u.val v.val;
  have h_lift : ∀ {a b : V₁} (q : G.Walk a b) (hq : ∀ x ∈ q.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ), ∃ p' : (auxGraph μ xstar i γ δ).Walk (Sum.inr ⟨a, by
    exact hq a ( by simp +decide )⟩) (Sum.inr ⟨b, by
    exact hq b ( by simp +decide )⟩), p'.length ≤ q.length := by
    intro a b q hq; induction' q with a b q ih <;> simp_all +decide ;
    all_goals generalize_proofs at *;
    rename_i h₁ h₂ h₃;
    obtain ⟨ p', hp' ⟩ := h₂;
    exact ⟨ SimpleGraph.Walk.cons ( by exact ⟨ by aesop, μ.adj_intersect _ _ ‹_› ⟩ ) p', by simp +arith +decide; linarith ⟩
  generalize_proofs at *;
  obtain ⟨ p', hp' ⟩ := h_lift p ( by
    intro x hx
    have h_dist : G.dist xstar x ≤ G.dist xstar u.val + G.dist u.val x ∧ G.dist xstar u.val ≤ G.dist xstar x + G.dist x u.val := by
      have h_triangle : ∀ (a b c : V₁), G.Reachable a b → G.Reachable b c → G.dist a c ≤ G.dist a b + G.dist b c := by
        intros a b c hab hbc
        obtain ⟨ p, hp ⟩ := hab.exists_walk_length_eq_dist
        obtain ⟨ q, hq ⟩ := hbc.exists_walk_length_eq_dist
        have h_walk : ∃ r : G.Walk a c, r.length ≤ p.length + q.length := by
          exact ⟨ p.append q, by simp +decide ⟩
        generalize_proofs at *;
        exact le_trans ( SimpleGraph.dist_le _ ) ( by linarith [ h_walk.choose_spec ] )
      generalize_proofs at *;
      exact ⟨ h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ), h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ) ⟩
    generalize_proofs at *;
    obtain ⟨ q, r, hqr ⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx;
    have h_dist : G.dist u.val x ≤ q.length ∧ G.dist x u.val ≤ q.length := by
      exact ⟨ SimpleGraph.dist_le q, by simpa [ SimpleGraph.dist_comm ] using SimpleGraph.dist_le q.reverse ⟩
    generalize_proofs at *;
    grind +suggestions )
  generalize_proofs at *;
  exact h_contra ⟨ p', hp'.trans hp.le ⟩

/-
On a geodesic from the root, the `k`-th vertex is at BFS distance exactly `k`.
-/
lemma geodesic_getVert_dist (hconn : G.Connected) (w : V₁) (p : G.Walk xstar w)
    (hp : p.length = G.dist xstar w) (k : ℕ) (hk : k ≤ p.length) :
    G.dist xstar (p.getVert k) = k := by
  refine' le_antisymm ( dist_getVert_le p k ) _;
  have h_triangle : G.dist xstar w ≤ G.dist xstar (p.getVert k) + G.dist (p.getVert k) w := by
    exact Connected.dist_triangle hconn;
  linarith [ dist_getVert_end_le p k, Nat.sub_add_cancel hk ]

/-
BFS predecessor: a vertex at distance `d+1` has a `G`-neighbour at distance `d`.
-/
lemma exists_bfs_pred (hconn : G.Connected) (w : V₁) (d : ℕ)
    (hw : G.dist xstar w = d + 1) :
    ∃ q : V₁, G.Adj w q ∧ G.dist xstar q = d := by
  -- By definition of distance, there exists a walk p from xstar to w with length d + 1.
  obtain ⟨p, hp⟩ : ∃ p : G.Walk xstar w, p.length = d + 1 := by
    obtain ⟨ p, hp ⟩ := hconn.exists_walk_length_eq_dist xstar w; use p; aesop;
  -- By geodesic_getVert_dist, G.dist xstar (p.getVert d) = d.
  have h_dist : G.dist xstar (p.getVert d) = d := by
    apply geodesic_getVert_dist;
    · exact hconn;
    · rw [hp, hw];
    · grind +revert;
  refine' ⟨ p.getVert d, _, h_dist ⟩;
  convert p.adj_getVert_succ ( by linarith : d < p.length ) |> SimpleGraph.Adj.symm using 1;
  rw [ ← hp, SimpleGraph.Walk.getVert_length ]

/-
**Layer lifting**: a `G`-walk between band vertices whose support lies entirely in BFS
layers `[i-γ+1, i+γ+δ]` lifts to an auxiliary-graph walk of no greater length.
-/
lemma walk_lift_band_layers (a b : BandIdx G xstar i γ δ) (q : G.Walk a.val b.val)
    (hq : ∀ x ∈ q.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ) :
    ∃ p : (auxGraph μ xstar i γ δ).Walk (Sum.inr a) (Sum.inr b), p.length ≤ q.length := by
  -- Apply the induction hypothesis to the walk from a to c and the walk from c to b.
  apply Classical.byContradiction
  intro h_contra;
  have h_lift : ∀ {a b : V₁} (q : G.Walk a b) (hq : ∀ x ∈ q.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ), ∃ p : (auxGraph μ xstar i γ δ).Walk (Sum.inr ⟨a, by
    exact hq a ( by simp +decide )⟩) (Sum.inr ⟨b, by
    exact hq b ( by simp +decide )⟩), p.length ≤ q.length := by
      intro a b q hq; induction' q with a b q ih <;> simp_all +decide ;
      rename_i h₁ h₂ h₃
      generalize_proofs at *;
      obtain ⟨ p, hp ⟩ := h₃; use SimpleGraph.Walk.cons ( by exact ⟨ by aesop, μ.adj_intersect _ _ ‹_› ⟩ ) p; simp +arith +decide; linarith;
  generalize_proofs at *;
  exact h_contra <| h_lift q hq

/-
**Boundary-component adjacency**: any boundary region (a connected component of `μ(w) \ C`
with `w` on layer `i-γ`) is `H`-adjacent to the low region `C`.  Since `w` (layer `i-γ ≥ 1`)
has a `G`-neighbour on layer `i-γ-1` whose region lies in `C`, `μ(w)` meets `C`; as `μ(w)` is
`H`-connected and the component avoids `C`, an edge of the component exits into `C`.
-/
lemma bdry_region_adj_low (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i)
    (v' : BdryIdx μ xstar i γ) :
    ∃ x ∈ auxRegion μ xstar i γ δ (Sum.inl v'),
      ∃ y ∈ lowRegion μ xstar i γ, H.Adj x y := by
  obtain ⟨q, hq⟩ : ∃ q : V₁, G.Adj v'.val.1 q ∧ G.dist xstar q = i - γ - 1 := by
    have h_dist : G.dist xstar v'.val.1 = i - γ := by
      exact v'.2.1;
    have := exists_bfs_pred ( hconn := hconn ) ( w := v'.val.1 ) ( d := i - γ - 1 ) ?_ <;> simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ i - γ from Nat.sub_pos_of_lt ( by omega ) ) ];
    exact this ‹_›
  generalize_proofs at *; (
  have h_meet : ∃ c ∈ μ.region v'.val.1, c ∈ μ.region q := by
    exact μ.adj_intersect _ _ hq.1 |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, hc₂ ⟩
  generalize_proofs at *; (
  obtain ⟨c, hc⟩ := h_meet
  have hc_in_C : c ∈ lowRegion μ xstar i γ := by
    exact Set.mem_iUnion₂.mpr ⟨ q, by omega, hc.2 ⟩
  generalize_proofs at *; (
  have h_walk : ∃ r : H.Walk v'.val.2 c, ∀ x ∈ r.support, x ∈ μ.region v'.val.1 := by
    exact μ.region_connected _ _ _ v'.property.2.1 hc.1 |> fun ⟨ r, hr ⟩ => ⟨ r, hr ⟩
  generalize_proofs at *; (
  obtain ⟨r, hr⟩ := h_walk
  have h_claim : ∀ (z : V₂) (r : H.Walk z c), (∀ x ∈ r.support, x ∈ μ.region v'.val.1) → z ∈ auxRegion μ xstar i γ δ (Sum.inl v') → (∃ x ∈ auxRegion μ xstar i γ δ (Sum.inl v'), ∃ y ∈ lowRegion μ xstar i γ, H.Adj x y) := by
    intros z r hr hz
    induction' r with z' r' ih
    generalize_proofs at *; (
    exact False.elim ( hz |> fun h => by have := compIn_subset ( auxHost μ xstar i γ ) ( μ.region v'.val.1 \ lowRegion μ xstar i γ ) v'.val.2 h; aesop ));
    by_cases h : ih ∈ lowRegion μ xstar i γ <;> simp_all +decide [ SimpleGraph.Walk.support_cons ];
    · exact ⟨ r', hz, ih, h, by assumption ⟩;
    · rename_i h₁ h₂ h₃
      generalize_proofs at *; (
      apply h₂ r h₃
      generalize_proofs at *; (
      obtain ⟨ p, hp ⟩ := hz
      generalize_proofs at *; (
      exact ⟨ p.append ( SimpleGraph.Walk.cons ( by exact ⟨ by assumption, by aesop ⟩ ) SimpleGraph.Walk.nil ), fun x hx => by rw [ SimpleGraph.Walk.support_append ] at hx; aesop ⟩)))
  generalize_proofs at *; (
  exact h_claim _ r hr ( compIn_self _ ⟨ v'.property.2.1, v'.property.2.2 ⟩ ))))))

/-
For a band centre `u`, there is a boundary vertex `v'` within auxiliary-graph distance
`γ+δ` of `u`.  Take a geodesic `xstar → u`; its vertices on layers `i-γ` and `i-γ+1` give a
boundary component meeting the band, reachable from `u` along the geodesic suffix.
-/
lemma exists_bdry_near (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (_hγδ : δ ≤ γ)
    (u : BandIdx G xstar i γ δ) (_hu1 : i + 1 ≤ G.dist xstar u.val)
    (hu2 : G.dist xstar u.val ≤ i + δ) :
    ∃ v' : BdryIdx μ xstar i γ,
      (auxGraph μ xstar i γ δ).Reachable (Sum.inr u) (Sum.inl v') ∧
      (auxGraph μ xstar i γ δ).dist (Sum.inr u) (Sum.inl v') ≤ γ + δ := by
  obtain ⟨ p, hp ⟩ := hconn.exists_walk_length_eq_dist xstar u.val;
  -- Set wmid := p.getVert (i-γ), wnext := p.getVert (i-γ+1). Note i-γ ≤ dU and i-γ+1 ≤ dU (since i-γ+1 ≤ i+1 ≤ dU).
  set wmid := p.getVert (i - γ)
  set wnext := p.getVert (i - γ + 1)
  have hwmid : G.dist xstar wmid = i - γ := by
    apply geodesic_getVert_dist; exact hconn; exact hp; exact (by omega)
  have hwnext : G.dist xstar wnext = i - γ + 1 := by
    apply geodesic_getVert_dist;
    · exact hconn;
    · exact hp;
    · omega
  have h_adj : G.Adj wmid wnext := by
    convert p.adj_getVert_succ _ using 1
    generalize_proofs at *; (
    omega)
  generalize_proofs at *; (
  obtain ⟨a, ha⟩ : ∃ a ∈ μ.region wmid, a ∈ μ.region wnext ∧ a ∉ lowRegion μ xstar i γ := by
    obtain ⟨ a, ha ⟩ := μ.adj_intersect wmid wnext h_adj;
    have h_not_in_lowRegion : μ.region wnext ∩ lowRegion μ xstar i γ = ∅ := by
      apply band_region_disjoint μ xstar i γ hconn hi wnext (by omega)
    generalize_proofs at *; (
    exact ⟨ a, ha.1, ha.2, fun h => h_not_in_lowRegion.subset ⟨ ha.2, h ⟩ ⟩)
  generalize_proofs at *; (
  -- Package wnext as a BandIdx wnext' (its distance i-γ+1 is in [i-γ+1, i+γ+δ]).
  set wnext' : BandIdx G xstar i γ δ := ⟨wnext, by
    omega⟩
  generalize_proofs at *; (
  -- Edge: (auxGraph μ xstar i γ δ).Adj (Sum.inr wnext') (Sum.inl v'): auxRegion (Sum.inr wnext') = μ.region wnext ∋ a, and auxRegion (Sum.inl v') = compIn … ∋ a (compIn_self, since a ∈ μ.region wmid \ lowRegion), so regions meet; the two vertices differ (inr vs inl). This gives a one-edge auxiliary walk e1 : (auxGraph …).Walk (Sum.inr wnext') (Sum.inl v') of length 1.
  obtain ⟨v', hv'⟩ : ∃ v' : BdryIdx μ xstar i γ, (auxGraph μ xstar i γ δ).Adj (Sum.inr wnext') (Sum.inl v') := by
    use ⟨(wmid, a), ⟨hwmid, ha.1, ha.2.2⟩⟩
    generalize_proofs at *; (
    constructor <;> simp_all +decide;
    exact ⟨ a, ha, ⟨ SimpleGraph.Walk.nil, by aesop ⟩ ⟩)
  generalize_proofs at *; (
  -- Suffix: q := p.drop (i-γ+1) : G.Walk wnext u.val, with q.length = dU - (i-γ+1). Every x ∈ q.support is p.getVert m for some m with i-γ+1 ≤ m ≤ dU (drop support consists of the later vertices; use SimpleGraph.Walk.getVert_drop and that support members are getVert at indices ≥ the drop amount), so G.dist xstar x = m ∈ [i-γ+1, i+δ] ⊆ [i-γ+1, i+γ+δ]. Apply walk_lift_band_layers wnext' u q (with this band-layer hypothesis) to get e2 : (auxGraph …).Walk (Sum.inr wnext') (Sum.inr u) of length ≤ q.length = dU - (i-γ+1).
  obtain ⟨q, hq⟩ : ∃ q : G.Walk wnext u.val, q.length ≤ G.dist xstar u.val - (i - γ + 1) ∧ ∀ x ∈ q.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ := by
    use p.drop (i - γ + 1);
    simp +zetaDelta at *;
    refine' ⟨ _, _ ⟩;
    · omega;
    · intro x hx
      obtain ⟨m, hm⟩ : ∃ m, i - γ + 1 ≤ m ∧ m ≤ p.length ∧ x = p.getVert m := by
        obtain ⟨ m, hm ⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
        generalize_proofs at *; (
        grind +suggestions)
      generalize_proofs at *; (
      grind +suggestions)
  generalize_proofs at *; (
  obtain ⟨p', hp'⟩ : ∃ p' : (auxGraph μ xstar i γ δ).Walk (Sum.inr wnext') (Sum.inr u), p'.length ≤ q.length := by
    exact walk_lift_band_layers μ xstar i γ δ wnext' u q hq.2 |> fun ⟨ p', hp' ⟩ => ⟨ p', hp' ⟩
  generalize_proofs at *; (
  use v';
  refine' ⟨ ⟨ SimpleGraph.Walk.append p'.reverse ( SimpleGraph.Walk.cons hv' SimpleGraph.Walk.nil ) ⟩, _ ⟩;
  refine' le_trans ( SimpleGraph.dist_le ( SimpleGraph.Walk.append p'.reverse ( SimpleGraph.Walk.cons hv' SimpleGraph.Walk.nil ) ) ) _ ; simp +arith +decide;
  omega))))))

/-
**Neighbourhood lift**: a vertex `v` within `G`-distance `γ` of a band centre `u` packages
as a band vertex and is within auxiliary-graph distance `γ` of `u` (reachably).
-/
lemma band_nbhd_lift (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (_hγδ : δ ≤ γ)
    (u : BandIdx G xstar i γ δ) (hu1 : i + 1 ≤ G.dist xstar u.val)
    (hu2 : G.dist xstar u.val ≤ i + δ) (v : V₁)
    (_hvr : G.Reachable u.val v) (hvd : G.dist u.val v ≤ γ) :
    ∃ (hv : i - γ + 1 ≤ G.dist xstar v ∧ G.dist xstar v ≤ i + γ + δ),
      (auxGraph μ xstar i γ δ).Reachable (Sum.inr u) (Sum.inr ⟨v, hv⟩) ∧
      (auxGraph μ xstar i γ δ).dist (Sum.inr u) (Sum.inr ⟨v, hv⟩) ≤ γ := by
  have h_support : ∀ x ∈ (hconn.exists_walk_length_eq_dist u.val v).choose.support, i - γ + 1 ≤ G.dist xstar x ∧ G.dist xstar x ≤ i + γ + δ := by
    intro x hx
    have h_dist : G.dist xstar x ≤ G.dist xstar u.val + G.dist u.val x ∧ G.dist xstar u.val ≤ G.dist xstar x + G.dist x u.val := by
      have h_triangle : ∀ (a b c : V₁), G.Reachable a b → G.Reachable b c → G.dist a c ≤ G.dist a b + G.dist b c := by
        intros a b c hab hbc
        obtain ⟨ p, hp ⟩ := hab.exists_walk_length_eq_dist
        obtain ⟨ q, hq ⟩ := hbc.exists_walk_length_eq_dist
        have h_walk : ∃ r : G.Walk a c, r.length ≤ p.length + q.length := by
          exact ⟨ p.append q, by simp +decide ⟩
        generalize_proofs at *; (
        exact le_trans ( SimpleGraph.dist_le _ ) ( by linarith [ h_walk.choose_spec ] ))
      generalize_proofs at *; (
      exact ⟨ h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ), h_triangle _ _ _ ( hconn _ _ ) ( hconn _ _ ) ⟩)
    generalize_proofs at *; (
    have h_dist_x : G.dist u.val x ≤ G.dist u.val v := by
      obtain ⟨ q, r, hqr ⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx
      generalize_proofs at *; (
      have := ‹∃ p : G.Walk ( u : V₁ ) v, p.length = G.dist ( u : V₁ ) v›.choose_spec; simp_all +decide [ SimpleGraph.Walk.length_append ] ;
      exact le_trans ( SimpleGraph.dist_le q ) ( by linarith ))
    generalize_proofs at *; (
    grind +suggestions));
  obtain ⟨ p, hp ⟩ := walk_lift_band_layers μ xstar i γ δ u ⟨ v, h_support v ( by simp ) ⟩ ( hconn.exists_walk_length_eq_dist u.val v ).choose h_support;
  refine' ⟨ _, ⟨ p ⟩, le_trans ( SimpleGraph.dist_le p ) _ ⟩;
  exact hp.trans ( by linarith [ hconn.exists_walk_length_eq_dist u.val v |> Classical.choose_spec ] )

/-! ## The band-center set in the auxiliary graph -/

/-- The set of auxiliary centers: band vertices (BFS layers `[i+1, i+δ]`) that lie in `S`. -/
def auxCenters (S : Set V₁) : Set (AuxV μ xstar i γ δ) :=
  {w | ∃ u : BandIdx G xstar i γ δ, w = Sum.inr u ∧ u.val ∈ S ∧
        i + 1 ≤ G.dist xstar u.val ∧ G.dist xstar u.val ≤ i + δ}

/-
**Model extension (contrapositive)**: if `G` has no `(μ, S, γ, t)`-model, then the
auxiliary graph has no `(μ', auxCenters, γ+δ, t-1)`-model.  Any such `(t-1)`-model extends to a
`(μ, S, γ, t)`-model by adjoining the centre `xstar` and the bag `T_t = μ(V_{0,i-γ-1})` (the
low region).
-/
lemma no_aux_model (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (hγδ : δ ≤ γ)
    (S : Set V₁) (hxstar : xstar ∈ S) (t : ℕ) (ht : 1 ≤ t)
    (hno : IsEmpty (MuModel μ S γ t)) :
    IsEmpty (MuModel (auxModel μ xstar i γ δ hconn hi) (auxCenters μ xstar i γ δ S) (γ + δ)
      (t - 1)) := by
  contrapose! hno; rcases t with ( _ | t ) <;> simp_all +decide ;
  obtain ⟨ M ⟩ := hno;
  -- Step A: choose u_k : BandIdx G xstar i γ δ such that M.center k = Sum.inr u_k.
  obtain ⟨u, hu⟩ : ∃ u : Fin t → BandIdx G xstar i γ δ, ∀ k, M.center k = Sum.inr (u k) ∧ (u k).val ∈ S ∧ i+1 ≤ G.dist xstar (u k).val ∧ G.dist xstar (u k).val ≤ i+δ := by
    have h_center_mem : ∀ k, ∃ u : BandIdx G xstar i γ δ, M.center k = Sum.inr u ∧ u.val ∈ S ∧ i+1 ≤ G.dist xstar u.val ∧ G.dist xstar u.val ≤ i+δ := by
      intro k
      obtain ⟨u, hu⟩ := M.center_mem k
      generalize_proofs at *; (
      use u)
    generalize_proofs at *; (
    exact ⟨ fun k => Classical.choose ( h_center_mem k ), fun k => Classical.choose_spec ( h_center_mem k ) ⟩)
  generalize_proofs at *; (
  -- Step B: prove four lemmas about the bags of M and the low region.
  have h_region_subset : ∀ k, μ.region (u k).val ⊆ M.bag k := by
    intro k
    have := M.neighborhood_contained k (M.center k) (SimpleGraph.Reachable.refl _) (by simp)
    simp [hu k] at this
    exact this
  have h_disjoint : ∀ k, Disjoint (M.bag k) (lowRegion μ xstar i γ) := by
    intro k
    obtain ⟨a0, ha0, ha0C⟩ : ∃ a0 ∈ μ.region (u k).val, a0 ∉ lowRegion μ xstar i γ := by
      have hemp := band_region_disjoint μ xstar i γ hconn hi (u k).val (by have := (hu k).2.2.1; omega)
      generalize_proofs at *; (
      exact Exists.elim ( μ.region_nonempty ( u k |>.1 ) ) fun x hx => ⟨ x, hx, fun hx' => hemp.subset ⟨ hx, hx' ⟩ ⟩)
    generalize_proofs at *; (
    have := M.neighborhood_contained k ( M.center k ) ( SimpleGraph.Reachable.refl _ ) ( by simp +decide [ hu k ] ) ; simp_all +decide ;
    exact Set.disjoint_left.mpr fun z hz hzC => by have := restrictHost_support_notMem ( M.connected k a0 z ( this ( by aesop ) ) hz |>.choose ) ha0C z ( by simp [ SimpleGraph.Walk.end_mem_support ] ) hzC; aesop;)
  have h_adjacent : ∀ k, ∃ a ∈ M.bag k, ∃ b ∈ lowRegion μ xstar i γ, H.Adj a b := by
    intro k
    obtain ⟨v', hreach, hdist⟩ := exists_bdry_near μ xstar i γ δ hconn hi hγδ (u k) (hu k).2.2.1 (hu k).2.2.2
    have hsub : auxRegion μ xstar i γ δ (Sum.inl v') ⊆ M.bag k := by
      have := M.neighborhood_contained k ( Sum.inl v' ) ( by simpa [ hu k ] using hreach ) ( by simpa [ hu k ] using hdist ) ; simpa using this;
    generalize_proofs at *; (
    obtain ⟨ a, ha, b, hb, hab ⟩ := bdry_region_adj_low μ xstar i γ δ hconn hi v'
    generalize_proofs at *; (exact ⟨ a, hsub ha, b, hb, hab ⟩ ))
  have h_nbhd : ∀ k, ∀ v, G.Reachable (u k).val v → G.dist (u k).val v ≤ γ → μ.region v ⊆ M.bag k := by
    intro k v hvr hvd
    obtain ⟨hv, hreach, hd2⟩ := band_nbhd_lift μ xstar i γ δ hconn hi hγδ (u k) (hu k).2.2.1 (hu k).2.2.2 v hvr hvd
    have := M.neighborhood_contained k (Sum.inr ⟨v, hv⟩) (by simpa [(hu k).1] using hreach) (by simp [(hu k).1]; omega); simpa using this
  generalize_proofs at *; (
  refine' ⟨ { bag := Fin.lastCases ( lowRegion μ xstar i γ ) ( fun k => M.bag k ), center := Fin.lastCases xstar ( fun k => ( u k ).val ), nonempty := _, connected := _, disjoint := _, adjacent := _, center_mem := _, neighborhood_contained := _ } ⟩ <;> simp +decide [ Fin.lastCases ];
  all_goals intro j; induction j using Fin.reverseInduction <;> simp +decide [ * ] ;
  exact lowRegion_nonempty μ xstar i γ hconn;
  exact M.nonempty _;
  exact fun a b ha hb => lowRegion_connected μ xstar i γ hconn a b ha hb |> fun ⟨ p, hp ⟩ => ⟨ p, hp ⟩
  generalize_proofs at *; (
  exact fun a b ha hb => M.connected _ _ _ ha hb |> fun ⟨ w, hw ⟩ => ⟨ w.map ( SimpleGraph.Hom.ofLE ( restrictHost_le H ( lowRegion μ xstar i γ ) ) ), fun x hx => by simpa using hw x ( by simpa using hx ) ⟩);
  exact fun j hj => by cases j using Fin.lastCases <;> simp_all +decide [ Fin.ext_iff, Disjoint.symm ] ;
  · intro j hj; cases j using Fin.lastCases <;> simp_all +decide [ Fin.ext_iff ] ;
    exact M.disjoint _ _ ( by simpa [ Fin.ext_iff ] using hj );
  · intro j hj; cases j using Fin.lastCases <;> simp_all +decide [ Fin.ext_iff ] ;
    exact Exists.elim ( h_adjacent _ ) fun a ha => Exists.elim ha.2 fun b hb => ⟨ b, hb.1, a, ha.1, hb.2.symm ⟩;
  · intro j hj; cases j using Fin.lastCases <;> simp_all +decide [ Fin.ext_iff ] ;
    rename_i k hk;
    rename_i k';
    convert M.adjacent k' k ( by simpa [ Fin.ext_iff ] using hj ) using 1;
    ext; simp [auxHost];
    exact fun _ => ⟨ fun ⟨ b, hb, hab ⟩ => ⟨ b, hb, hab, fun h => h_disjoint k' |>.le_bot ⟨ by assumption, h ⟩, fun h => h_disjoint k |>.le_bot ⟨ by assumption, h ⟩ ⟩, fun ⟨ b, hb, hab, _, _ ⟩ => ⟨ b, hb, hab ⟩ ⟩;
  · intro v hv hv'; exact Set.subset_iUnion₂_of_subset v ( by omega ) le_rfl;
  · exact h_nbhd _))

end Aux

end BandPartition