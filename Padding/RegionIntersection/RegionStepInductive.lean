/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.AsymptoticDimension
import Padding.Defs.MuModel
import Padding.RegionIntersection.AsymptoticDimensionHelpers
import Padding.RegionIntersection.IntersectionModel
import Padding.RegionIntersection.BandAssembly

/-! # The inductive step of `region_step`

This file carries out the `t ≥ 3` inductive step of the Bonamy–Bousquet–Esperet–Groenland–
Pirot–Scott region-step lemma, following `AsymptoticDimensionProof.tex`.

Fix a connected `G`, a region intersection model `μ` of `G` over `H`, a set `S`, and a BFS
root `x* ∈ S`.  Write `D v = G.dist x* v` for the BFS distance.  We split `S` into:

* the **central** ball `central = {v | D v ≤ 2γ+1}` (diameter `≤ 4γ+2`), and
* **bands** `band k = {v | 2γ+2+kδ ≤ D v ≤ 2γ+1+(k+1)δ}` for `k : ℕ`.

The central ball plus the bands tile the reachable part of `G` (all of `V₁` here, as `G` is
connected).  Two bands `band k`, `band k'` with `k ≠ k'`, and the central ball versus any
odd band, are `δ`-separated (BFS layers are `1`-Lipschitz).  The technical heart
(`band_partition`) applies the induction hypothesis on an auxiliary intersection graph to
partition each band; the assembly then interleaves the two parity classes (even bands; the
central ball together with the odd bands) using `combine_indexed_separated` and
`combine_separated_partitions`.

The diameter radius is `ρ = 4γ + 4(t-2)δ + 2` (see `AsymptoticDimension.lean`).
-/

open SimpleGraph Set

namespace RegionStepInductive

universe u

variable {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}

/-- The central ball: vertices within BFS distance `2γ+1` of the root. -/
def centralSet (G : SimpleGraph V₁) (xstar : V₁) (γ : ℕ) : Set V₁ :=
  {v | G.dist xstar v ≤ 2 * γ + 1}

/-- The `k`-th BFS band: vertices with BFS distance in `[2γ+2+kδ, 2γ+1+(k+1)δ]`. -/
def bandSet (G : SimpleGraph V₁) (xstar : V₁) (γ δ k : ℕ) : Set V₁ :=
  {v | 2 * γ + 2 + k * δ ≤ G.dist xstar v ∧ G.dist xstar v ≤ 2 * γ + 1 + (k + 1) * δ}

/-! ## BFS layering: 1-Lipschitz separation -/

/-- BFS distance is 1-Lipschitz: `|D u - D v| ≤ G.dist u v`. Concretely, the bound we need:
`G.dist xstar v ≤ G.dist xstar u + G.dist u v`. -/
lemma bfs_triangle (G : SimpleGraph V₁) (hconn : G.Connected) (xstar u v : V₁) :
    G.dist xstar v ≤ G.dist xstar u + G.dist u v :=
  hconn.dist_triangle (u := xstar) (v := u) (w := v)

/-- Separation from the BFS layering: if the BFS distances of `u` and `v` differ by more
than `δ`, then `G.dist u v > δ`. -/
lemma sep_of_bfs_gap (G : SimpleGraph V₁) (hconn : G.Connected) (xstar u v : V₁) (δ : ℕ)
    (h : G.dist xstar u + δ < G.dist xstar v) : δ < G.dist u v := by
  have := bfs_triangle G hconn xstar u v
  omega

/-! ## Central ball: bounded diameter -/

/-- Two vertices in the central ball are within `4γ+2` of each other (via the root). -/
lemma central_diam (G : SimpleGraph V₁) (xstar : V₁) (γ : ℕ) (hconn : G.Connected)
    (u v : V₁) (hu : u ∈ centralSet G xstar γ) (hv : v ∈ centralSet G xstar γ) :
    G.dist u v ≤ 4 * γ + 2 := by
  have h1 : G.dist u v ≤ G.dist u xstar + G.dist xstar v :=
    hconn.dist_triangle (u := u) (v := xstar) (w := v)
  rw [SimpleGraph.dist_comm (u := u) (v := xstar)] at h1
  simp only [centralSet, Set.mem_setOf_eq] at hu hv
  omega

/-- The central ball admits a trivial `(δ, 4γ+2)`-partition with any positive number of
labels (all vertices get label `0`). -/
def centralPartition (G : SimpleGraph V₁) (xstar : V₁) (γ δ m : ℕ) (hm : 0 < m)
    (hconn : G.Connected) (S : Set V₁) :
    DeltaRhoPartition G δ (4 * γ + 2) (S ∩ centralSet G xstar γ) m where
  label _ := ⟨0, hm⟩
  component_radius u v hu hv _ _ :=
    central_diam G xstar γ hconn u v hu.2 hv.2

/-! ## The technical core: partitioning a single band

For each band `band k`, the induction hypothesis applied to the auxiliary intersection
graph `G'_{i-γ, i+γ+δ}` (with `i = 2γ+1+kδ`) yields a `(δ, ρ)`-partition of `S ∩ band k`
in `G` of size `2^{t-3}`.  This is the heart of the construction (model extension + IH +
distance transfer from `G'` to `G`).
-/

/-- **Band partition** (technical core, now fully proved). Given the induction hypothesis
`ih` and the absence of a `(μ, S, γ, t)`-model, each band `S ∩ band k` admits a
`(δ, ρ)`-partition of size `2^{t-3}` in `G`.

This is the genuinely research-level step of the BBEGPS proof (following
`AsymptoticDimensionProof.tex`), with `i = 2γ+1+kδ`.  The construction is carried out in
`BandPartition.lean` (the auxiliary intersection graph `G' = G'_{i-γ, i+γ+δ}`, the
model-extension lemma `no_aux_model`, and the `G ↔ G'` distance transfer), in
`InduceComponent.lean` (applying the connected-graph induction hypothesis to each connected
component of the — possibly disconnected — auxiliary graph), and assembled in
`BandAssembly.lean` (`band_partition_core`).  Here we only instantiate `i = 2γ+1+kδ` and
rewrite `bandSet` to the `[i+1, i+δ]` layer description.

Key points of the construction:

1. The auxiliary graph `G'` is the intersection graph of: the connected components of
   `μ(v) \ μ(V_{0,i-γ-1})` over the boundary layer `v ∈ V_{i-γ}`, together with the band
   vertices `V_{i-γ+1, i+γ+δ}` (region `μ(u)`).  Its host is `H` with edges restricted to
   the complement of the low region `μ(V_{0,i-γ-1})`, so every auxiliary bag is automatically
   disjoint from `T_t = μ(V_{0,i-γ-1})`, resolving the disjointness-vs-adjacency tension.
2. **Model extension** (`BandPartition.no_aux_model`): a `(μ', band-centres, γ+δ, t-1)`-model
   extends to a `(μ, S, γ, t)`-model by adjoining `x_t = x*`, `T_t = μ(V_{0,i-γ-1})`; the
   boundary components keep `H`-adjacency to `T_t`.  Contrapositively, the absence of a
   `(μ,S,γ,t)`-model rules out every such `(t-1)`-model in `G'`.
3. The induction hypothesis is applied to each connected component of `G'`
   (`InduceComponent`), and the resulting partitions are pulled back to `G` and combined via
   `combine_indexed_separated`, with the inter-component separation supplied by the
   `G → G'` step-lifting lemma `BandPartition.step_lift`. -/
theorem band_partition
    (μ : RegionIntersectionModel G H) (S : Set V₁) (t γ δ : ℕ)
    (ih : ∀ m, m < t → 2 ≤ m → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
        {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
        δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' m) →
        Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (m - 2) * δ + 2) S' (2 ^ (m - 2))))
    (ht3 : 3 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ t))
    (xstar : V₁) (hxstar : xstar ∈ S) (k : ℕ) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2)
      (S ∩ bandSet G xstar γ δ k) (2 ^ (t - 3))) := by
  have key := BandPartition.band_partition_core μ S t γ δ (2 * γ + 1 + k * δ) ih ht3 hγδ hδ
    (by omega) hconn hno_model xstar hxstar
  have hkd : (k + 1) * δ = k * δ + δ := by ring
  have hset : S ∩ {v | (2 * γ + 1 + k * δ) + 1 ≤ G.dist xstar v ∧
      G.dist xstar v ≤ (2 * γ + 1 + k * δ) + δ} = S ∩ bandSet G xstar γ δ k := by
    unfold bandSet
    ext v
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor <;> rintro ⟨hS, h1, h2⟩ <;> exact ⟨hS, by omega, by omega⟩
  rwa [hset] at key

/-! ## Assembly -/

/-
Combine the even bands, the odd bands, and the central ball into a single
`(δ, ρ)`-partition of `S` of size `2 · 2^{t-3} = 2^{t-2}`.
-/
theorem assemble_partition
    (G : SimpleGraph V₁) (xstar : V₁) (S : Set V₁) (γ δ ρ m : ℕ)
    (hconn : G.Connected)
    (hcover : ∀ v ∈ S, v ∈ centralSet G xstar γ ∨ ∃ k, v ∈ bandSet G xstar γ δ k)
    (Pc : DeltaRhoPartition G δ ρ (S ∩ centralSet G xstar γ) m)
    (Pb : ∀ k, DeltaRhoPartition G δ ρ (S ∩ bandSet G xstar γ δ k) m) :
    Nonempty (DeltaRhoPartition G δ ρ S (2 * m)) := by
  obtain ⟨Pa⟩ : Nonempty (DeltaRhoPartition G δ ρ (⋃ j, S ∩ bandSet G xstar γ δ (2 * j)) m) := by
    apply combine_indexed_separated (fun j => Pb (2 * j)) (by
    intro i j hij u hu v hv;
    -- Without loss of generality, assume $i < j$.
    wlog hij' : i < j generalizing i j u v hu hv;
    · simpa only [ SimpleGraph.dist_comm ] using this j i ( Ne.symm hij ) v hv u hu ( lt_of_le_of_ne ( le_of_not_gt hij' ) ( Ne.symm hij ) );
    · have h_dist : G.dist xstar u ≤ 2 * γ + 1 + (2 * i + 1) * δ ∧ 2 * γ + 2 + 2 * j * δ ≤ G.dist xstar v := by
        exact ⟨ hu.2.2, hv.2.1 ⟩;
      exact sep_of_bfs_gap G hconn xstar u v δ ( by nlinarith ));
  obtain ⟨Pb⟩ : Nonempty (DeltaRhoPartition G δ ρ (S ∩ centralSet G xstar γ ∪ ⋃ j, S ∩ bandSet G xstar γ δ (2 * j + 1)) m) := by
    convert combine_indexed_separated _ _;
    rotate_left;
    exact Option ℕ;
    exact ⟨ none ⟩;
    use fun i => i.elim ( S ∩ centralSet G xstar γ ) fun j => S ∩ bandSet G xstar γ δ ( 2 * j + 1 );
    · rintro ( _ | j ) <;> [ exact Pc; exact Pb _ ];
    · rintro ( _ | i ) ( _ | j ) hij u hu v hv <;> simp_all +decide [ bandSet ];
      · exact sep_of_bfs_gap G hconn xstar u v δ ( by nlinarith [ hu.2.out ] );
      · have := RegionStepInductive.sep_of_bfs_gap G hconn xstar v u δ ?_;
        · rwa [ SimpleGraph.dist_comm ];
        · nlinarith [ hv.2.out ];
      · have h_dist : G.dist xstar u + δ < G.dist xstar v ∨ G.dist xstar v + δ < G.dist xstar u := by
          cases lt_or_gt_of_ne hij <;> first | left; nlinarith | right; nlinarith;
        cases' h_dist with h_dist h_dist <;> [ exact sep_of_bfs_gap G hconn xstar u v δ h_dist; exact sep_of_bfs_gap G hconn xstar v u δ h_dist |> fun h => by rwa [ SimpleGraph.dist_comm ] at h ];
    · ext; simp [Set.mem_union, Set.mem_iUnion];
      constructor;
      · rintro ( ⟨ h₁, h₂ ⟩ | ⟨ h₁, k, hk ⟩ ) <;> [ exact ⟨ none, h₁, h₂ ⟩ ; exact ⟨ some k, h₁, hk ⟩ ];
      · rintro ⟨ i, hi ⟩ ; cases i <;> aesop;
  have h_union : (⋃ j, S ∩ bandSet G xstar γ δ (2 * j)) ∪ (S ∩ centralSet G xstar γ ∪ ⋃ j, S ∩ bandSet G xstar γ δ (2 * j + 1)) = S := by
    ext v; specialize hcover v; by_cases hv : v ∈ S <;> simp_all +decide ;
    rcases hcover with ( h | ⟨ k, hk ⟩ ) <;> [ exact Or.inr ( Or.inl h ) ; exact Or.imp ( fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩ ) ( fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩ ) ( Nat.even_or_odd' k ) |> Or.imp id ( Or.inr ) ];
    rcases Nat.even_or_odd' k with ⟨ i, rfl | rfl ⟩ <;> [ exact Or.inl ⟨ i, hk ⟩ ; exact Or.inr <| Or.inr ⟨ i, hk ⟩ ];
  exact h_union ▸ combine_separated_partitions Pa Pb

/-! ## The inductive step -/

/-- **Inductive step of `region_step`** (`t ≥ 3`). -/
theorem region_step_inductive
    (μ : RegionIntersectionModel G H) (S : Set V₁) (t γ δ : ℕ)
    (ih : ∀ m, m < t → 2 ≤ m → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
        {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
        δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' m) →
        Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (m - 2) * δ + 2) S' (2 ^ (m - 2))))
    (ht3 : 3 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ t)) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2) S (2 ^ (t - 2))) := by
  set ρ := 4 * γ + 4 * (t - 2) * δ + 2 with hρ
  -- If `S` is empty, any labelling works.
  rcases S.eq_empty_or_nonempty with hSempty | ⟨xstar, hxstar⟩
  · refine ⟨⟨fun _ => ⟨0, by positivity⟩, ?_⟩⟩
    intro u v hu; rw [hSempty] at hu; exact absurd hu (by simp)
  · -- Central partition (with `2^{t-3}` labels).
    have hm : 0 < 2 ^ (t - 3) := by positivity
    have hcentral_le : 4 * γ + 2 ≤ ρ := by
      have : 0 ≤ 4 * (t - 2) * δ := Nat.zero_le _
      omega
    have Pc : DeltaRhoPartition G δ ρ (S ∩ centralSet G xstar γ) (2 ^ (t - 3)) :=
      (centralPartition G xstar γ δ (2 ^ (t - 3)) hm hconn S).mono_rho hcentral_le
    -- Band partitions.
    have Pb : ∀ k, DeltaRhoPartition G δ ρ (S ∩ bandSet G xstar γ δ k) (2 ^ (t - 3)) := by
      intro k
      exact (band_partition μ S t γ δ ih ht3 hγδ hδ hconn hno_model xstar hxstar k).some
    -- Cover: every vertex of `S` is in the central ball or some band.
    have hcover : ∀ v ∈ S, v ∈ centralSet G xstar γ ∨ ∃ k, v ∈ bandSet G xstar γ δ k := by
      intro v _
      simp only [centralSet, bandSet, Set.mem_setOf_eq]
      set d := G.dist xstar v with hd
      by_cases hc : d ≤ 2 * γ + 1
      · exact Or.inl hc
      · right
        set q := (d - (2 * γ + 2)) / δ with hq
        have hmod : q * δ + (d - (2 * γ + 2)) % δ = d - (2 * γ + 2) := by
          rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
        have hr : (d - (2 * γ + 2)) % δ < δ := Nat.mod_lt _ hδ
        refine ⟨q, ?_, ?_⟩
        · omega
        · simp only [add_mul, one_mul]; omega
    -- Assemble.
    have hsize : 2 * 2 ^ (t - 3) = 2 ^ (t - 2) := by
      have : t - 2 = (t - 3) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [← hsize]
    exact assemble_partition G xstar S γ δ ρ (2 ^ (t - 3)) hconn hcover Pc Pb

end RegionStepInductive

/-- Bridge to the name used in `AsymptoticDimension.lean`. -/
theorem region_step_inductive {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    {t δ : ℕ}
    (ih : ∀ m, m < t → 2 ≤ m → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
        {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
        δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' m) →
        Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (m - 2) * δ + 2) S' (2 ^ (m - 2))))
    (S : Set V₁) (γ : ℕ)
    (ht3 : 3 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ)
    (hconn : G.Connected)
    (hno_model : IsEmpty (MuModel μ S γ t)) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2) S (2 ^ (t - 2))) :=
  RegionStepInductive.region_step_inductive μ S t γ δ ih ht3 hγδ hδ hconn hno_model