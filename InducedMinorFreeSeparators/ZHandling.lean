/-
# Z-Handling for Pure Pairs Dichotomy

Helper lemmas for handling "heavy" vertices (Z = {v : w(v) > δ}) in the proof of
pure_pairs_vwsp_dichotomy. The main results are:

1. Z vertices are pairwise far apart in the VWSP light metric
2. Induced minor transfers from induced subgraph to the full graph
3. Distance equivalence: short distances in G agree with distances in G[V\Z]
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.CoarsePurePairs
import InducedMinorFreeSeparators.VWSPProperties

open Set Function CoarsePurePairs SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Z vertices are pairwise far -/

/-
Any walk from x to y (x ≠ y) has light weight ≥ (w x + w y) / 2.
    This is because the first edge contributes ≥ w(x)/2 and the last ≥ w(y)/2,
    and for walks of length 1, the single edge contributes (w(x)+w(y))/2.
-/
omit [Fintype V] in
lemma walk_light_weight_ge_endpoints {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {x y : V} (hxy : x ≠ y)
    (p : G.Walk x y) :
    (w x + w y) / 2 ≤ p.edgeWeightSumLight w := by
  induction' p with u v p ih;
  · contradiction;
  · by_cases h : p = ih <;> simp_all +decide [ Walk.edgeWeightSumLight ];
    · grind +suggestions;
    · linarith [ hw v, hw p, hw ih ]

/-
For distinct vertices with w(x) > δ and w(y) > δ,
    the VWSP light distance is > δ.
-/
lemma z_vertices_far_light {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {x y : V} (hxy : x ≠ y) {δ : ℝ}
    (hx : δ < w x) (hy : δ < w y) :
    δ < @dist V (vwspPMSLight G w hw hconn).toDist x y := by
  obtain ⟨ p, hp ⟩ := weightedDistLight_achieved hw hconn x y;
  convert lt_of_lt_of_le ( show δ < ( w x + w y ) / 2 by linarith ) ( walk_light_weight_ge_endpoints hw hxy p ) using 1;
  convert hp.symm

/-! ## Induced minor transfer from subgraph to full graph -/

/-
An induced minor of G.comap f gives an induced minor of G,
    provided f is injective.
-/
lemma hasInducedMinor_internal_of_comap {α β γ : Type*}
    (f : β → α) (hf : Function.Injective f)
    (G : SimpleGraph α) (H : SimpleGraph γ)
    (h : HasInducedMinor_internal (G.comap f) H) :
    HasInducedMinor_internal G H := by
  cases' h with model;
  use fun w => f '' model.branch w;
  · intro w;
    have h_iso : (SimpleGraph.comap f G).induce (model.branch w) ≃g G.induce (f '' model.branch w) := by
      refine' { Equiv.ofBijective ( fun x => ⟨ f x, by aesop ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> aesop;
    exact h_iso.symm.connected_iff.mpr ( model.branch_connected w );
  · exact fun w₁ w₂ h => Set.disjoint_image_of_injective hf ( model.branch_disjoint w₁ w₂ h );
  · intro w₁ w₂ h; rcases model.adj_preserved w₁ w₂ h with ⟨ v₁, hv₁, v₂, hv₂, h ⟩ ; use f v₁, Set.mem_image_of_mem f hv₁, f v₂, Set.mem_image_of_mem f hv₂; aesop;
  · intro w₁ w₂ hw₁w₂ hw₁w₂' v₁ hv₁ v₂ hv₂ h; obtain ⟨ u₁, hu₁, rfl ⟩ := hv₁; obtain ⟨ u₂, hu₂, rfl ⟩ := hv₂; have := model.nonadj_preserved w₁ w₂ hw₁w₂ hw₁w₂' u₁ hu₁ u₂ hu₂; simp_all +decide [ SimpleGraph.comap_adj ] ;

/-! ## Distance equivalence: short distances agree -/

/-
On a walk with endpoints having w ≤ δ and total light weight ≤ δ,
    every vertex on the walk has w ≤ δ.
    For interior vertices: the two adjacent edges contribute ≥ w(v).
    For endpoints: given by hypothesis.
-/
omit [Fintype V] [DecidableEq V] in
lemma walk_support_weight_le {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {a b : V}
    (p : G.Walk a b) {δ : ℝ} (hp : p.edgeWeightSumLight w ≤ δ)
    (ha : w a ≤ δ) (hb : w b ≤ δ)
    {v : V} (hv : v ∈ p.support) : w v ≤ δ := by
  induction' p with u v p ih generalizing δ;
  · cases hv ; aesop;
    contradiction;
  · cases' eq_or_ne p ih with h h <;> simp_all +decide [ Walk.edgeWeightSumLight ];
    · grind;
    · rename_i k hk₁ hk₂;
      have h_edge_weight : Walk.edgeWeightSumLight w hk₁ ≥ (w p + w (hk₁.getVert 1)) / 2 := by
        rcases hk₁ with ( _ | ⟨ _, _, hk₁ ⟩ ) <;> simp_all +decide [ Walk.edgeWeightSumLight ];
        exact add_nonneg ( div_nonneg ( add_nonneg ( hw _ ) ( hw _ ) ) zero_le_two ) ( edgeWeightSumLight_nonneg hw _ );
      grind

/-
A walk in G whose vertices all lie in S can be lifted to a walk in G.comap Subtype.val
    (the induced subgraph on S), preserving the light weight.
-/
omit [Fintype V] [DecidableEq V] in
lemma walk_lift_to_subgraph {G : SimpleGraph V}
    {S : Set V} {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (p : G.Walk a b) (hp : ∀ v ∈ p.support, v ∈ S) :
    ∃ (p' : (G.comap (Subtype.val : S → V)).Walk ⟨a, ha⟩ ⟨b, hb⟩),
      ∀ (w : V → ℝ), p'.edgeWeightSumLight (w ∘ Subtype.val) = p.edgeWeightSumLight w := by
  induction' p with a b c p ih;
  · exact ⟨ SimpleGraph.Walk.nil, fun w => rfl ⟩;
  · obtain ⟨ p', hp' ⟩ := ‹∀ ( ha : c ∈ S ) ( hb : p ∈ S ), ( ∀ v ∈ _, v ∈ S ) → ∃ p', ∀ w : V → ℝ, Walk.edgeWeightSumLight ( w ∘ Subtype.val ) p' = Walk.edgeWeightSumLight w _› ( hp _ <| by simp +decide ) hb ( fun v hv => hp _ <| by simp +decide [ hv ] );
    use Walk.cons ( by aesop ) p';
    simp +decide [ *, Walk.edgeWeightSumLight ]

/-
For a, b with w(a) ≤ δ, w(b) ≤ δ and d_G(a,b) ≤ δ:
    the optimal walk avoids heavy vertices, so d_{G.comap} ≤ d_G.
-/
lemma vwsp_light_dist_restrict_le {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {δ : ℝ} (_hδ : 0 ≤ δ)
    {S : Set V} (hS : ∀ v ∈ S, w v ≤ δ) (hS_complete : ∀ v, w v ≤ δ → v ∈ S)
    (_hconn' : (G.comap (Subtype.val : S → V)).Connected)
    {x y : S}
    (hd : G.weightedDistLight w x.val y.val ≤ δ) :
    (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y ≤
    G.weightedDistLight w x.val y.val := by
  obtain ⟨ p, hp ⟩ := weightedDistLight_achieved hw hconn x y;
  refine' le_trans ( ciInf_le _ _ ) _;
  exact ⟨ 0, Set.forall_mem_range.2 fun p => by
    exact edgeWeightSumLight_nonneg ( fun v => hw v.val ) p ⟩;
  exact Classical.choose ( walk_lift_to_subgraph x.2 y.2 p ( fun v hv => hS_complete v ( walk_support_weight_le hw p ( by linarith ) ( hS x x.2 ) ( hS y y.2 ) hv ) ) );
  grind +suggestions

/-
Contrapositive: d_{G.comap} > δ implies d_G > δ.
-/
lemma vwsp_light_dist_gt_of_restrict_gt {G : SimpleGraph V}
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    {δ : ℝ} (hδ : 0 ≤ δ)
    {S : Set V} (hS : ∀ v ∈ S, w v ≤ δ)
    (hS_complete : ∀ v, w v ≤ δ → v ∈ S)
    (hconn' : (G.comap (Subtype.val : S → V)).Connected)
    {x y : S}
    (hd : δ < (G.comap (Subtype.val : S → V)).weightedDistLight (w ∘ Subtype.val) x y) :
    δ < G.weightedDistLight w x.val y.val := by
  contrapose! hd;
  refine' le_trans _ hd;
  apply vwsp_light_dist_restrict_le hw hconn hδ hS hS_complete hconn' hd

/-! ## Splitting a finset into well-separated halves -/

/-
If S is a finset of pairwise-far vertices (all pairwise d > δ) with
    |S| ≥ 2k, then S can be split into A, B with |A| ≥ k, |B| ≥ k,
    and all pairs between A, B are > δ apart.
-/
omit [Fintype V] in
lemma split_far_finset_into_halves
    {S : Finset V} {k : ℕ} (hk : 2 * k ≤ S.card)
    {d : V → V → ℝ} {δ : ℝ}
    (hfar : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ < d a b) :
    ∃ (A B : Finset V), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧
    k ≤ A.card ∧ k ≤ B.card ∧
    ∀ a ∈ A, ∀ b ∈ B, δ < d a b := by
  -- By Lemma 25, there exists � a� subset A of S with |A| � =� k.
  obtain ⟨A, hA⟩ : ∃ A : Finset V, A ⊆ S ∧ A.card = k := by
    exact Finset.exists_subset_card_eq ( by linarith );
  refine' ⟨ A, S \ A, hA.1, _, _, hA.2.ge, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_sdiff ];
  · grind +ring;
  · exact fun a ha b hb hab => hfar a ( hA.1 ha ) b hb ( by rintro rfl; exact hab ha )

end
