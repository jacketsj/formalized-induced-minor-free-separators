/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Padding.PaddedDecompDefs
import Padding.PaddedDecomp.Bartal

/-! # Helper Lemmas for Bartal's Padded Modulus Bound

This file contains the combinatorial infrastructure used in the proof of
`bartal_has_padded_modulus` (in `HasPaddedModulus.lean`).

Key results:
- `card_perm_min_eq`: In a random permutation, each element of a set S is equally
  likely to have the smallest image.
- `greedyBallPart'`: The greedy ball-carving partition construction.
- `greedy_padding_count'`: Per-point padding count bound.
-/

open PaddedDecomposition MeasureTheory Metric Set Real Finset BigOperators

namespace PaddedDecomposition

noncomputable section

open Classical

set_option maxHeartbeats 1600000

/-! ## First Element Counting -/

/-- In a random permutation, each element of a nonempty set S is equally likely to have
    the smallest image. -/
lemma card_perm_min_eq (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (s : Fin n) (hs : s ∈ S) :
    (Finset.univ.filter (fun (perm : _root_.Equiv.Perm (Fin n)) =>
      ∀ s' ∈ S, perm s ≤ perm s')).card * S.card =
    Fintype.card (_root_.Equiv.Perm (Fin n)) := by
  have h_perm : ∀ s' ∈ S, (Finset.filter (fun perm : Equiv.Perm (Fin n) => ∀ s'' ∈ S, perm s' ≤ perm s'') (Finset.univ : Finset (Equiv.Perm (Fin n)))).card = (Finset.filter (fun perm : Equiv.Perm (Fin n) => ∀ s'' ∈ S, perm s ≤ perm s'') (Finset.univ : Finset (Equiv.Perm (Fin n)))).card := by
    intro s' hs'
    refine' Finset.card_bij ( fun perm _ => perm * Equiv.swap s s' ) _ _ _ <;> simp +decide [ Equiv.swap_apply_def ]
    · grind
    · intro b hb; use b * Equiv.swap s s'; aesop
  have h_perm2 : Finset.card (Finset.univ : Finset (Equiv.Perm (Fin n))) = Finset.sum S (fun s' => Finset.card (Finset.filter (fun perm : Equiv.Perm (Fin n) => ∀ s'' ∈ S, perm s' ≤ perm s'') (Finset.univ : Finset (Equiv.Perm (Fin n))))) := by
    rw [ ← Finset.card_biUnion ]
    · congr with perm; simp +decide
      exact Finset.exists_min_image _ _ hS
    · intros s' hs' s'' hs'' hss''; simp_all +decide [ Finset.disjoint_left ]
      exact fun perm hperm => ⟨ s', hs', lt_of_le_of_ne ( hperm s'' hs'' ) fun h => hss'' <| perm.injective h ⟩
  rw [ Finset.sum_congr rfl ‹_› ] at h_perm2; simp_all +decide [ mul_comm ]

/-- Corollary: counting permutations where first element of S is in A ⊆ S. -/
lemma card_perm_min_in_subset (n : ℕ) (S A : Finset (Fin n)) (hAS : A ⊆ S)
    (hS : S.Nonempty) :
    A.card * Fintype.card (_root_.Equiv.Perm (Fin n)) ≤
    (Finset.univ.filter (fun (p : _root_.Equiv.Perm (Fin n)) =>
      ∃ a ∈ A, ∀ s' ∈ S, p a ≤ p s')).card * S.card := by
  have h1 : ∀ a ∈ A, (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ∀ s' ∈ S, p a ≤ p s')).card * S.card = Fintype.card (Equiv.Perm (Fin n)) :=
    fun a ha => card_perm_min_eq n S hS a ( hAS ha )
  have h2 : (Finset.biUnion A (fun a => Finset.univ.filter (fun p : Equiv.Perm (Fin n) => ∀ s' ∈ S, p a ≤ p s'))).card * S.card = A.card * Fintype.card (Equiv.Perm (Fin n)) := by
    rw [ Finset.card_biUnion ]
    · rw [ Finset.sum_mul _ _ _ ]; rw [ Finset.sum_congr rfl h1 ]; simp +decide
    · intros a ha b hb hab; simp_all +decide [ Finset.disjoint_left ]
      exact fun p hp => ⟨ a, hAS ha, lt_of_le_of_ne ( hp b ( hAS hb ) ) ( by intro h; have := p.injective h; aesop ) ⟩
  rw [ ← h2 ]; exact Nat.mul_le_mul_right _ ( Finset.card_mono <| by aesop_cat )

/-! ## Greedy Ball-Carving Partition -/

variable {X : Type*} [MetricSpace X] [Fintype X]

/-- The greedy ball-carving partition. -/
noncomputable def greedyBallPart' (σ : Fin (Fintype.card X) ≃ X) (R : ℝ) (hR : 0 ≤ R) :
    Partition X where
  label x :=
    (Finset.univ.filter (fun i : Fin (Fintype.card X) => dist x (σ i) ≤ R)).min'
      ⟨σ.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hR]⟩⟩

/-- The greedy partition is Δ-bounded when 2R ≤ Δ. -/
lemma greedyBallPart'_isBounded (σ : Fin (Fintype.card X) ≃ X) (R Δ : ℝ)
    (hR : 0 ≤ R) (hΔ : 2 * R ≤ Δ) :
    (greedyBallPart' σ R hR).IsBounded Δ := by
  intro z
  refine' Metric.ediam_le_of_forall_dist_le _
  intro x hx y hy
  obtain ⟨c, hc⟩ : ∃ c : X, dist x c ≤ R ∧ dist y c ≤ R := by
    simp_all +decide [ Partition.cluster, greedyBallPart' ]
    use σ (Finset.min' (Finset.univ.filter (fun i : Fin (Fintype.card X) => dist z (σ i) ≤ R)) (by
      exact ⟨ σ.symm z, by simp +decide [ hR ] ⟩))
    generalize_proofs at *
    exact ⟨ by simpa [ Fin.ext hx ] using Finset.min'_mem ( Finset.filter ( fun i => dist x ( σ i ) ≤ R ) Finset.univ ) ‹_›, by simpa [ Fin.ext hy ] using Finset.min'_mem ( Finset.filter ( fun i => dist y ( σ i ) ≤ R ) Finset.univ ) ‹_› ⟩
  linarith [ dist_triangle_right x y c ]

/-- Sufficient condition for padding in the greedy partition. -/
lemma greedyBallPart'_padded (σ : Fin (Fintype.card X) ≃ X) (R ρ : ℝ)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (_hρR : ρ ≤ R) (z : X)
    (hk : dist z (σ ((Finset.univ.filter (fun j : Fin (Fintype.card X) =>
      dist z (σ j) ≤ R + ρ)).min' ⟨σ.symm z, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simp; linarith [dist_self z]⟩⟩)) ≤ R - ρ) :
    Metric.closedBall z ρ ⊆ (greedyBallPart' σ R hR).cluster z := by
  generalize_proofs at *
  intro w hw; simp_all +decide [ greedyBallPart', Partition.cluster ]
  refine' le_antisymm _ _ <;> simp +decide [ Finset.min' ]
  · intro b hb
    refine' ⟨ Finset.min' ( Finset.univ.filter fun j => dist z ( σ j ) ≤ R + ρ ) ‹_›, _, _ ⟩
    · exact le_trans ( dist_triangle _ _ _ ) ( by linarith )
    · exact Finset.min'_le _ _ ( by simpa using by linarith )
  · intro b hb; use Finset.min' ( Finset.univ.filter fun j => dist z ( σ j ) ≤ R + ρ ) ‹_›; simp_all +decide [ dist_comm ]
    exact ⟨ by linarith, Finset.min'_le _ _ ( by simpa using by linarith [ dist_triangle z w ( σ b ) ] ) ⟩

/-! ## Counting Lemma for Equivalences -/

omit [MetricSpace X] in
/-- Counting lemma for equivalences. -/
lemma card_equiv_first_in_subset' (S A : Finset X) (hAS : A ⊆ S) (hS : S.Nonempty) :
    A.card * Fintype.card (Fin (Fintype.card X) ≃ X) ≤
    (Finset.univ.filter (fun σ : Fin (Fintype.card X) ≃ X =>
      ∃ a ∈ A, ∀ s ∈ S, σ.symm a ≤ σ.symm s)).card * S.card := by
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card X) ≃ X) := ⟨Fintype.equivOfCardEq <| by simp +decide⟩
  have h_bij : Finset.card (Finset.filter (fun σ : Fin (Fintype.card X) ≃ X => ∃ a ∈ A, ∀ s ∈ S, σ.symm a ≤ σ.symm s) Finset.univ) = Finset.card (Finset.filter (fun p : Fin (Fintype.card X) ≃ Fin (Fintype.card X) => ∃ a' ∈ Finset.image e.symm A, ∀ s' ∈ Finset.image e.symm S, p.symm a' ≤ p.symm s') Finset.univ) := by
    refine' Finset.card_bij ( fun σ _ => σ.trans e.symm ) _ _ _ <;> simp +decide [ Finset.mem_image ]
    · intro a₁ x hx₁ hx₂ a₂ y hy₁ hy₂ h; ext i; replace h := Equiv.congr_fun h i; aesop
    · intro b x hx hb; use b.trans e; aesop
  convert card_perm_min_in_subset ( Fintype.card X ) ( Finset.image e.symm S ) ( Finset.image e.symm A ) _ _ using 1
  · rw [ Finset.card_image_of_injective _ e.symm.injective ]
    exact congr_arg _ ( Fintype.card_congr ( Equiv.ofBijective ( fun f => f.trans e.symm ) ⟨ fun f g h => by ext i; simpa using congr_arg ( fun f => f i ) h, fun f => ⟨ f.trans e, by ext i; simp ⟩ ⟩ ) )
  · rw [ Finset.card_image_of_injective _ e.symm.injective ]
    have h_bij2 : Finset.card (Finset.filter (fun p : Fin (Fintype.card X) ≃ Fin (Fintype.card X) => ∃ a' ∈ Finset.image e.symm A, ∀ s' ∈ Finset.image e.symm S, p.symm a' ≤ p.symm s') Finset.univ) = Finset.card (Finset.filter (fun p : Fin (Fintype.card X) ≃ Fin (Fintype.card X) => ∃ a' ∈ Finset.image e.symm A, ∀ s' ∈ Finset.image e.symm S, p a' ≤ p s') Finset.univ) := by
      refine' Finset.card_bij ( fun p hp => p.symm ) _ _ _ <;> simp +decide
      · exact fun a₁ x hx₁ hx₂ a₂ y hy₁ hy₂ h => by simpa using congr_arg Equiv.symm h
      · exact fun b x hx hx' => ⟨ b.symm, ⟨ x, hx, fun y hy => by simpa using hx' y hy ⟩, by simp +decide ⟩
    grobner
  · exact Finset.image_subset_image hAS
  · exact ⟨ _, Finset.mem_image_of_mem _ hS.choose_spec ⟩

/-- Per-point bound for greedy padding count. -/
lemma greedy_padding_count' (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 ≤ ρ) (hρβ : ρ ≤ β) (z : X) :
    (Finset.univ.filter (fun w : X => dist z w ≤ β - ρ)).card *
      Fintype.card (Fin (Fintype.card X) ≃ X) ≤
    (Finset.univ.filter (fun σ : Fin (Fintype.card X) ≃ X =>
      Metric.closedBall z ρ ⊆ (greedyBallPart' σ β hβ.le).cluster z)).card *
    (Finset.univ.filter (fun w : X => dist z w ≤ β + ρ)).card := by
  refine' le_trans _ ( mul_le_mul_left ( Finset.card_le_card _ ) _ )
  convert card_equiv_first_in_subset' _ _ _ _
  · grind
  · exact ⟨ z, by simpa using by linarith ⟩
  · intro σ hσ
    simp +zetaDelta at *
    obtain ⟨ a, ha₁, ha₂ ⟩ := hσ
    refine' greedyBallPart'_padded σ β ρ hβ.le hρ hρβ z _
    convert ha₁ using 1
    rw [ show Finset.min' ( Finset.filter ( fun j => dist z ( σ j ) ≤ β + ρ ) Finset.univ ) ⟨ σ.symm a, by simpa using ha₁.trans ( by linarith ) ⟩ = σ.symm a from ?_ ]
    · rw [ Equiv.apply_symm_apply ]
    · refine' le_antisymm _ _ <;> simp +decide [ Finset.min' ]
      · exact ⟨ σ.symm a, by simpa using ha₁.trans ( by linarith ), le_rfl ⟩
      · exact fun b hb => ha₂ _ hb |> le_trans <| by simp +decide

/-! ## Pigeonhole -/

/-- Pigeonhole for natural-valued functions. -/
lemma exists_ge_of_sum_ge' {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℕ) (c : ℕ) (h : c * Fintype.card α ≤ ∑ x, f x) :
    ∃ x, c ≤ f x := by
  contrapose! h
  simpa [ mul_comm ] using Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ => h x

end

end PaddedDecomposition
