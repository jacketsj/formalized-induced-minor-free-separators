/-
# Separator transfer for an arbitrary forbidden induced minor

This file contains the part of the improved separator theorem which is
independent of the new exponential-carving argument.  In particular, it keeps
the exact `45 * sqrt (|V H| + |E H|)` dependence of the concurrent-flow
theorem instead of specializing the forbidden graph to a subdivided clique.
-/
import InducedMinorFreeSeparators.MainTheoremProof

open Finset BigOperators

variable {V W : Type*}

private lemma card_ge_two_of_edge' [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : 1 ≤ G.edgeFinset.card) : 2 ≤ Fintype.card V := by
  contrapose! hm
  interval_cases _ : Fintype.card V
  · simp_all +decide [Fintype.card_eq_zero_iff]
    exact Subsingleton.elim _ _
  · rw [Fintype.card_eq_one_iff] at *
    aesop

/-- The Korhonen--Lokshtanov spread lower bound, with an arbitrary forbidden
induced minor and its exact vertex/edge parameter. -/
theorem induced_minor_free_spread_lower
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hconn : G.Connected)
    (hfree : ¬G.ContainsInducedMinor H)
    (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 /
        (45 * Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
          Real.sqrt (G.edgeFinset.card : ℝ)) ≤ Qspread G := by
  haveI : Nonempty V := hconn.nonempty
  rw [lp_strong_duality G hconn]
  apply QDual_ge_of_cf_bound hconn
  intro cf
  exact congestion_lower_bound_of_no_induced_minor G H cf
    (fun hm => hfree (hasInducedMinor_imp_containsInducedMinor hm)) hV

/-- Transfer an arbitrary hereditary spread comparison into a separator,
retaining the exact flow factor `45 * sqrt (|V H| + |E H|)`. -/
theorem separator_of_general_spread_bound
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hm : 1 ≤ G.edgeFinset.card)
    (hfree : ¬G.ContainsInducedMinor H)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hbound : ∀ (S : Finset V), 2 ≤ S.card → S.Nonempty →
        (G.induce (↑S : Set V)).Connected →
        Qspread (G.induce (↑S : Set V)) ≤
          ρ * Qbar (G.induce (↑S : Set V))) :
    G.HasBalancedSeparator (2 / 3)
      (4 * (45 *
        Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) * ρ)) := by
  have hn : 2 ≤ Fintype.card V := card_ge_two_of_edge' G hm
  have hflow : 0 < 45 *
      Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
      Real.sqrt (G.edgeFinset.card : ℝ) := by
    have hWpos : (0 : ℝ) < (Fintype.card W : ℝ) + H.edgeFinset.card := by
      have : 0 < Fintype.card W := Fintype.card_pos
      positivity
    have hmpos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast (by omega : 0 < G.edgeFinset.card)
    positivity
  apply embed_to_sep_v2 G
    (45 * Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
      Real.sqrt (G.edgeFinset.card : ℝ) * ρ)
    (mul_pos hflow hρ) hn
  intro S hS hSne hSconn
  have hcard : 2 ≤ Fintype.card {v // v ∈ (↑S : Set V)} := by
    simpa [Fintype.card_coe] using hS
  have hminor : ¬(G.induce (↑S : Set V)).ContainsInducedMinor H :=
    induced_minor_free_hereditary G H _ hfree
  have hspread := induced_minor_free_spread_lower
    (G.induce (↑S : Set V)) H hSconn hminor hcard
  have hedge := edgeFinset_card_induce_le G S
  have hsqrt : Real.sqrt ((G.induce (↑S : Set V)).edgeFinset.card : ℝ) ≤
      Real.sqrt (G.edgeFinset.card : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hedge)
  have hden : 45 * Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
        Real.sqrt ((G.induce (↑S : Set V)).edgeFinset.card : ℝ) ≤
      45 * Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) := by
    gcongr
  have hsubedges : 0 < (G.induce (↑S : Set V)).edgeFinset.card := by
    haveI : Nontrivial {v // v ∈ (↑S : Set V)} :=
      Fintype.one_lt_card_iff_nontrivial.mp (by simpa [Fintype.card_coe] using hS)
    have hne : G.induce (↑S : Set V) ≠ ⊥ := by
      intro heq
      rw [heq] at hSconn
      exact SimpleGraph.not_connected_bot hSconn
    exact Finset.card_pos.mpr (SimpleGraph.edgeFinset_nonempty.mpr hne)
  have hnum : (Fintype.card {v // v ∈ (↑S : Set V)} : ℝ) = S.card := by
    simp [Fintype.card_coe]
  rw [hnum] at hspread
  have hlower : (S.card : ℝ) ^ 2 /
      (45 * Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ)) ≤
      Qspread (G.induce (↑S : Set V)) := by
    refine le_trans ?_ hspread
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  have hcomparison := hbound S hS hSne hSconn
  have hflow' : 0 < 45 *
      Real.sqrt ((Fintype.card W : ℝ) + H.edgeFinset.card) *
      Real.sqrt (G.edgeFinset.card : ℝ) := hflow
  have := le_trans hlower hcomparison
  rw [div_le_iff₀ hflow', ← mul_assoc] at this
  rw [div_le_iff₀ (mul_pos hflow' hρ)]
  nlinarith
