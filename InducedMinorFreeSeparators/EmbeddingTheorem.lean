/-
# Embedding Theorem and SP-to-Embed Bound

Derives Q(G) ≤ 625h² · Q̄(G) for K_h^(1)-IMF graphs by:
1. SP-to-embed bound (Proposition 2.1): Q ≤ α·Q̄ from embedding existence
2. Coarse pure pairs dichotomy + Rabinovich embeddings (Theorem 1.5)
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.MetricEmbeddings
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.PurePairsDichotomy

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Embedding Theorem (Theorem 1.5) -/

omit [DecidableEq V] in
theorem embedding_from_dichotomy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hn : 0 < Fintype.card V) :
    ∃ f : V → ℝ,
      (∀ u v, |f u - f v| ≤ G.weightedDist w u v) ∧
      (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
        625 * (h : ℝ) ^ 2 * ∑ u : V, ∑ v : V, |f u - f v|) := by
  letI pms := vwspPMS G w hw hconn
  obtain hdic | hdic := pure_pairs_dichotomy G h hh hconn hIMF w hw hn
  · obtain ⟨x₀, S, hx₀, hS_ball, hS_size⟩ := hdic
    have h_core := large_core_case
      (1 / (32 * (h : ℝ) ^ 2)) 3 (by positivity) (by norm_num : (2:ℝ) < 3) hn
      S x₀ hx₀ hS_ball hS_size
    refine ⟨fun x => Metric.infDist x (↑S : Set V), fun u v => ?_, ?_⟩
    · exact (infDist_nonExpansive (↑S : Set V)) u v
    · change ∑ u, ∑ v, G.weightedDist w u v ≤ _
      have hD : pairDistSum V = ∑ u : V, ∑ v : V, G.weightedDist w u v := rfl
      rw [← hD]; unfold embeddingSum at h_core
      have hpds_nn : 0 ≤ pairDistSum V :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
      have hnum : pairDistSum V / (192 * (h : ℝ) ^ 2) =
        1 / (32 * (h : ℝ) ^ 2) / 2 * (1 - 2 / 3) * pairDistSum V := by ring
      have h_le : pairDistSum V / (625 * (h : ℝ) ^ 2) ≤
          pairDistSum V / (192 * (h : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hpds_nn (by positivity) (by nlinarith)
      have h625 : (0 : ℝ) < 625 * (h : ℝ) ^ 2 := by positivity
      linarith [(div_le_iff₀ h625).mp (le_trans h_le (hnum ▸ h_core))]
  · obtain ⟨A, B, hA_size, hB_size, hAB_dist⟩ := hdic
    have h_spread := well_spread_case
      (13 / (40 * (h : ℝ))) 33 (by positivity) (by norm_num : (0:ℝ) < 33) hn
      A B hA_size hB_size hAB_dist
    refine ⟨fun x => Metric.infDist x (↑A : Set V), fun u v => ?_, ?_⟩
    · exact (infDist_nonExpansive (↑A : Set V)) u v
    · change ∑ u, ∑ v, G.weightedDist w u v ≤ _
      have hD : pairDistSum V = ∑ u : V, ∑ v : V, G.weightedDist w u v := rfl
      rw [← hD]; unfold embeddingSum at h_spread
      have hpds_nn : 0 ≤ pairDistSum V :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
      have hnum : pairDistSum V / (52800 / 169 * (h : ℝ) ^ 2) =
        (13 / (40 * (h : ℝ))) ^ 2 / 33 * pairDistSum V := by ring
      have h_le : pairDistSum V / (625 * (h : ℝ) ^ 2) ≤
          pairDistSum V / (52800 / 169 * (h : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hpds_nn (by positivity) (by nlinarith)
      have h625 : (0 : ℝ) < 625 * (h : ℝ) ^ 2 := by positivity
      linarith [(div_le_iff₀ h625).mp (le_trans h_le (hnum ▸ h_spread))]

/-! ## SP-to-Embed Bound (Proposition 2.1) -/

omit [DecidableEq V] in
theorem sp_to_embed_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (α : ℝ) (hα : 0 < α)
    (h_embed : ∀ (w : V → ℝ), (∀ v, 0 ≤ w v) → (∑ v, w v ≤ 1) →
      ∃ f : V → ℝ,
        (∀ u v, G.Adj u v → |f u - f v| ≤ w u + w v) ∧
        (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
          α * ∑ u : V, ∑ v : V, |f u - f v|)) :
    Qspread G ≤ α * Qbar G := by
  unfold Qspread
  apply csSup_le
  · exact ⟨_, ⟨fun _ => 0, fun _ => le_refl _, by simp, rfl⟩⟩
  · rintro x ⟨w, hw_nn, hw_sum, rfl⟩
    obtain ⟨f, hf_edge, hf_dist⟩ := h_embed w hw_nn hw_sum
    have hfeas : QbarFeasible G w f := ⟨hw_nn, hw_sum, hf_edge⟩
    have hobj : QbarObj f ≤ Qbar G := Qbar_le_of_feasible G hconn hfeas
    unfold QbarObj at hobj
    linarith [mul_le_mul_of_nonneg_left hobj hα.le]

/-! ## Main derived result: Q ≤ 625h² · Q̄ -/

omit [DecidableEq V] in
theorem vwsp_embedding_for_sp_to_embed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (_hw_sum : ∑ v, w v ≤ 1)
    (hn : 0 < Fintype.card V) :
    ∃ f : V → ℝ,
      (∀ u v, G.Adj u v → |f u - f v| ≤ w u + w v) ∧
      (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
        625 * (h : ℝ) ^ 2 * ∑ u : V, ∑ v : V, |f u - f v|) := by
  obtain ⟨f, hf_ne, hf_dist⟩ := embedding_from_dichotomy G h hh hconn hIMF w hw hn
  exact ⟨f, fun u v hadj => le_trans (hf_ne u v) (weightedDist_le_edge hw hadj), hf_dist⟩

omit [DecidableEq V] in
theorem coarse_pure_pairs_bound_derived
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hconn : G.Connected)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h)) :
    Qspread G ≤ 625 * (h : ℝ) ^ 2 * Qbar G := by
  have hn : 0 < Fintype.card V := by
    rw [Fintype.card_pos_iff]; exact hconn.nonempty
  show Qspread G ≤ (625 * (h : ℝ) ^ 2) * Qbar G
  exact sp_to_embed_bound G hconn (625 * (h : ℝ) ^ 2) (by positivity)
    (fun w hw hw_sum => vwsp_embedding_for_sp_to_embed G h hh hconn hIMF w hw hw_sum hn)
