/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.RegionIntersection.BandPartition
import Padding.RegionIntersection.InduceComponent
import Padding.RegionIntersection.AsymptoticDimensionHelpers

/-! # Assembly of the band partition

Combining the auxiliary-graph tools (`BandPartition`) and the induced-component tools
(`InduceComponent`), this file proves `band_partition_core`: a single BFS band
`{v | i+1 ≤ D v ≤ i+δ} ∩ S` admits a `(δ, ρ)`-partition of size `2^{t-3}` in `G`.

The auxiliary graph `G' = auxGraph μ xstar i γ δ` is generally disconnected, so the induction
hypothesis (which needs a connected graph) is applied to each connected component of `G'`;
the per-component partitions are pulled back to `G` and combined using
`combine_indexed_separated`, with the separation between different components provided by the
`G → G'` step-lifting lemma `step_lift`.
-/

open SimpleGraph Set BandPartition

namespace BandPartition

universe u

variable {V₁ V₂ : Type u} {G : SimpleGraph V₁} {H : SimpleGraph V₂}

/-- The piece of the band corresponding to a connected component `c` of the auxiliary graph:
the band vertices in `S` whose auxiliary band-image lies in `c`. -/
def bandPieces (μ : RegionIntersectionModel G H) (xstar : V₁) (i γ δ : ℕ) (S : Set V₁)
    (c : (auxGraph μ xstar i γ δ).ConnectedComponent) : Set V₁ :=
  {v | ∃ (h1 : i + 1 ≤ G.dist xstar v) (h2 : G.dist xstar v ≤ i + δ), v ∈ S ∧
        (auxGraph μ xstar i γ δ).connectedComponentMk
          (Sum.inr ⟨v, ⟨by omega, by omega⟩⟩) = c}

/-
Different components give `δ`-separated pieces in `G`.
-/
lemma band_separation (μ : RegionIntersectionModel G H) (xstar : V₁) (i γ δ : ℕ)
    (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (hγδ : δ ≤ γ) (S : Set V₁)
    (c c' : (auxGraph μ xstar i γ δ).ConnectedComponent) (hcc : c ≠ c')
    (u : V₁) (hu : u ∈ bandPieces μ xstar i γ δ S c)
    (v : V₁) (hv : v ∈ bandPieces μ xstar i γ δ S c') :
    δ < G.dist u v := by
  contrapose! hcc;
  obtain ⟨h1u, h2u, huS, hcu⟩ := hu
  obtain ⟨h1v, h2v, hvS, hcv⟩ := hv;
  obtain ⟨p, hp⟩ := band_walk_lift μ xstar i γ δ hconn hi hγδ ⟨u, ⟨by omega, by omega⟩⟩ ⟨v, ⟨by omega, by omega⟩⟩ h1u h2u h1v h2v (le_trans hcc hγδ);
  rw [ ← hcu, ← hcv, SimpleGraph.ConnectedComponent.sound ];
  exact ⟨ p ⟩

/-
**Pullback of a component partition.**  A `(δ, ρ)`-partition of the connected component
`c` of the auxiliary graph (restricted to the band centres) pulls back to a `(δ, ρ)`-partition
of the corresponding band piece in `G`.
-/
lemma transfer_partition (μ : RegionIntersectionModel G H) (S : Set V₁) (γ δ i ρ k : ℕ)
    (xstar : V₁) (hconn : G.Connected) (hi : 2 * γ + 1 ≤ i) (hγδ : δ ≤ γ)
    (c : (auxGraph μ xstar i γ δ).ConnectedComponent)
    (Pc : DeltaRhoPartition ((auxGraph μ xstar i γ δ).induce c.supp) δ ρ
            {w : ↥c.supp | w.val ∈ auxCenters μ xstar i γ δ S} k) :
    Nonempty (DeltaRhoPartition G δ ρ (bandPieces μ xstar i γ δ S c) k) := by
  obtain ⟨w, hw⟩ : ∃ w, w ∈ c.supp := by
    exact c.exists_rep;
  set Sc := {w : ↥c.supp | w.val ∈ auxCenters μ xstar i γ δ S} with hSc_def;
  -- Define a total map `wmap : V₁ → ↥c.supp`.
  obtain ⟨wmap, hwmap⟩ : ∃ wmap : V₁ → ↥c.supp, ∀ v (h : v ∈ bandPieces μ xstar i γ δ S c), (wmap v).val = Sum.inr ⟨v, ⟨by obtain ⟨h1, h2, _, _⟩ := h; omega, by obtain ⟨h1, h2, _, _⟩ := h; omega⟩⟩ := by
    haveI := Classical.decPred ( fun v => v ∈ bandPieces μ xstar i γ δ S c );
    exact ⟨ fun v => if h : v ∈ bandPieces μ xstar i γ δ S c then ⟨ Sum.inr ⟨ v, ⟨ by obtain ⟨ h1, h2, _, _ ⟩ := h; omega, by obtain ⟨ h1, h2, _, _ ⟩ := h; omega ⟩ ⟩, by obtain ⟨ h1, h2, _, hcomp ⟩ := h; rw [ SimpleGraph.ConnectedComponent.mem_supp_iff ] ; exact hcomp ⟩ else ⟨ w, hw ⟩, fun v hv => by simp +decide [ hv ] ⟩;
  refine' ⟨ ⟨ fun v => Pc.label ( wmap v ), _ ⟩ ⟩;
  intro u v hu hv hlab hchain
  have hSc : ∀ v (h : v ∈ bandPieces μ xstar i γ δ S c), wmap v ∈ Sc := by
    intro v hv
    simp [Sc, hwmap v hv];
    obtain ⟨ h1, h2, hvS, hcomp ⟩ := hv; exact ⟨ ⟨ v, by omega, by omega ⟩, rfl, hvS, h1, h2 ⟩ ;
  have hstep : ∀ a b (ha : a ∈ bandPieces μ xstar i γ δ S c) (hb : b ∈ bandPieces μ xstar i γ δ S c), G.dist a b ≤ δ → (induce c.supp (auxGraph μ xstar i γ δ)).dist (wmap a) (wmap b) ≤ δ := by
    intros a b ha hb hab
    have hstep : (auxGraph μ xstar i γ δ).dist (Sum.inr ⟨a, ⟨by obtain ⟨h1, h2, _, _⟩ := ha; omega, by obtain ⟨h1, h2, _, _⟩ := ha; omega⟩⟩) (Sum.inr ⟨b, ⟨by obtain ⟨h1, h2, _, _⟩ := hb; omega, by obtain ⟨h1, h2, _, _⟩ := hb; omega⟩⟩) ≤ δ := by
      apply step_lift μ xstar i γ δ hconn hi hγδ ⟨a, ⟨by obtain ⟨h1, h2, _, _⟩ := ha; omega, by obtain ⟨h1, h2, _, _⟩ := ha; omega⟩⟩ ⟨b, ⟨by obtain ⟨h1, h2, _, _⟩ := hb; omega, by obtain ⟨h1, h2, _, _⟩ := hb; omega⟩⟩ (by obtain ⟨h1, h2, _, _⟩ := ha; omega) (by obtain ⟨h1, h2, _, _⟩ := ha; omega) (by obtain ⟨h1, h2, _, _⟩ := hb; omega) (by obtain ⟨h1, h2, _, _⟩ := hb; omega) hab;
    convert hstep using 1;
    rw [ ← hwmap a ha, ← hwmap b hb, induce_dist_eq_supp ];
  have hlift : Relation.ReflTransGen (fun a b => a ∈ Sc ∧ b ∈ Sc ∧ Pc.label a = Pc.label (wmap u) ∧ Pc.label b = Pc.label (wmap u) ∧ (induce c.supp (auxGraph μ xstar i γ δ)).dist a b ≤ δ) (wmap u) (wmap v) := by
    have hlift : ∀ {a b : V₁}, Relation.ReflTransGen (fun a b => a ∈ bandPieces μ xstar i γ δ S c ∧ b ∈ bandPieces μ xstar i γ δ S c ∧ Pc.label (wmap a) = Pc.label (wmap u) ∧ Pc.label (wmap b) = Pc.label (wmap u) ∧ G.dist a b ≤ δ) a b → Relation.ReflTransGen (fun a b => a ∈ Sc ∧ b ∈ Sc ∧ Pc.label a = Pc.label (wmap u) ∧ Pc.label b = Pc.label (wmap u) ∧ (induce c.supp (auxGraph μ xstar i γ δ)).dist a b ≤ δ) (wmap a) (wmap b) := by
      intros a b hab;
      induction hab;
      · exact .refl;
      · grind +qlia;
    exact hlift hchain;
  have hgc := Pc.component_radius (wmap u) (wmap v) (hSc u hu) (hSc v hv) hlab hlift;
  have := dist_proj_le μ xstar i γ δ hconn (wmap u) (wmap v) (by
  have hreach : (wmap u).val ∈ c.supp ∧ (wmap v).val ∈ c.supp := by
    exact ⟨ wmap u |>.2, wmap v |>.2 ⟩;
  exact SimpleGraph.ConnectedComponent.exact ( by aesop ));
  convert this.trans _;
  · exact hwmap u hu ▸ rfl;
  · exact hwmap v hv ▸ rfl;
  · grind +suggestions

/-- Each band piece admits a `(δ, ρ)`-partition of size `2^{t-3}` in `G`, obtained by applying
the induction hypothesis to the (connected) component `c` of the auxiliary graph and pulling
the partition back along the projection to `G`. -/
lemma band_piece_partition (μ : RegionIntersectionModel G H) (S : Set V₁) (t γ δ i : ℕ)
    (ih : ∀ m, m < t → 2 ≤ m → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
        {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
        δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' m) →
        Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (m - 2) * δ + 2) S' (2 ^ (m - 2))))
    (ht3 : 3 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ) (hi : 2 * γ + 1 ≤ i)
    (hconn : G.Connected) (hno_model : IsEmpty (MuModel μ S γ t))
    (xstar : V₁) (hxstar : xstar ∈ S)
    (c : (auxGraph μ xstar i γ δ).ConnectedComponent) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2)
      (bandPieces μ xstar i γ δ S c) (2 ^ (t - 3))) := by
  have hno' := no_aux_model μ xstar i γ δ hconn hi hγδ S hxstar t (by omega) hno_model
  have hGc := connectedComponent_induce_connected c
  have hnoc := induceModel_no_model (auxModel μ xstar i γ δ hconn hi) c
    (auxCenters μ xstar i γ δ S) (γ + δ) (t - 1) hno'
  obtain ⟨Pc⟩ := ih (t - 1) (by omega) (by omega)
    (induceModel (auxModel μ xstar i γ δ hconn hi) c.supp)
    {w : ↥c.supp | w.val ∈ auxCenters μ xstar i γ δ S} (γ + δ) (by omega) hGc hnoc
  have hr : 4 * (γ + δ) + 4 * (t - 1 - 2) * δ + 2 = 4 * γ + 4 * (t - 2) * δ + 2 := by
    rw [show t - 1 - 2 = t - 3 from by omega, show t - 2 = (t - 3) + 1 from by omega]; ring
  have hk : t - 1 - 2 = t - 3 := by omega
  rw [hr, hk] at Pc
  exact transfer_partition μ S γ δ i (4 * γ + 4 * (t - 2) * δ + 2) (2 ^ (t - 3))
    xstar hconn hi hγδ c Pc

/-
**Band partition** (core, with explicit layer index `i`).
-/
theorem band_partition_core (μ : RegionIntersectionModel G H) (S : Set V₁) (t γ δ i : ℕ)
    (ih : ∀ m, m < t → 2 ≤ m → ∀ {W₁ W₂ : Type u} {G' : SimpleGraph W₁}
        {H' : SimpleGraph W₂} (μ' : RegionIntersectionModel G' H') (S' : Set W₁) (γ' : ℕ),
        δ ≤ γ' → G'.Connected → IsEmpty (MuModel μ' S' γ' m) →
        Nonempty (DeltaRhoPartition G' δ (4 * γ' + 4 * (m - 2) * δ + 2) S' (2 ^ (m - 2))))
    (ht3 : 3 ≤ t) (hγδ : δ ≤ γ) (hδ : 1 ≤ δ) (hi : 2 * γ + 1 ≤ i)
    (hconn : G.Connected) (hno_model : IsEmpty (MuModel μ S γ t))
    (xstar : V₁) (hxstar : xstar ∈ S) :
    Nonempty (DeltaRhoPartition G δ (4 * γ + 4 * (t - 2) * δ + 2)
      (S ∩ {v | i + 1 ≤ G.dist xstar v ∧ G.dist xstar v ≤ i + δ}) (2 ^ (t - 3))) := by
  by_cases h : ∃ v, v ∈ S ∧ i + 1 ≤ G.dist xstar v ∧ G.dist xstar v ≤ i + δ;
  · obtain ⟨ v, hv₁, hv₂, hv₃ ⟩ := h;
    convert combine_indexed_separated ( fun c => ( band_piece_partition μ S t γ δ i ih ht3 hγδ hδ hi hconn hno_model xstar hxstar c ).some ) ( fun c1 c2 hc => band_separation μ xstar i γ δ hconn hi hγδ S c1 c2 hc ) using 1;
    · congr! 2;
      ext v; simp [bandPieces];
    · exact ⟨ ( auxGraph μ xstar i γ δ ).connectedComponentMk ( Sum.inr ⟨ v, ⟨ by omega, by omega ⟩ ⟩ ) ⟩;
  · refine' ⟨ ⟨ fun _ => ⟨ 0, by positivity ⟩, _ ⟩ ⟩;
    grind

end BandPartition