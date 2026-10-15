/- # Logarithmic embedding from residual exponential carving -/
import InducedMinorFreeSeparators.ResidualStructural
import InducedMinorFreeSeparators.EmbeddingTheorem

open Finset BigOperators Metric Set
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The endpoint-heavy vertex-weighted shortest-path metric embeds in the line
with distortion logarithmic in the size of the forbidden subdivided graph. -/
theorem logarithmic_vwsp_embedding_internal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hconn : G.Connected)
    (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (H : SimpleGraph (Fin h)) (hmH : H.edgeSet.ncard = m)
    (hfree : ¬HasInducedMinor_internal G (graphOneSubdiv H))
    (hn : 2 ≤ Fintype.card V) :
    ∃ f : V → ℝ,
      (∀ u v, |f u - f v| ≤ G.weightedDist w u v) ∧
      (∑ u : V, ∑ v : V, G.weightedDist w u v ≤
        65536 * Real.log (8 * ((3 * h + m + 7 : ℕ) : ℝ)) *
          ∑ u : V, ∑ v : V, |f u - f v|) := by
  letI pms := vwspPMSLight G w hw hconn
  set M : ℕ := 3 * h + m + 7
  have hM : 2 ≤ M := by dsimp [M]; omega
  by_cases hD : pairDistSum V = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro u v
      simp only [sub_self, abs_zero]
      letI : Nonempty (G.Walk u v) := ⟨(hconn u v).some⟩
      exact le_ciInf fun p => edgeWeightSum_nonneg hw p
    · have hheavy : (∑ u : V, ∑ v : V, G.weightedDist w u v) =
          2 * pairDistSum V := by
        rw [← pairDistSum_heavy_eq_two_light G w hw hconn]
        rfl
      rw [hheavy, hD]
      simp
  have hDpos : 0 < pairDistSum V := lt_of_le_of_ne
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (Ne.symm hD)
  have hcores :
      (∀ x : V, 2 * (Finset.univ.filter fun y : V =>
          dist x y ≤ pairDistSum V /
            (4 * (Fintype.card V : ℝ) ^ 2)).card < Fintype.card V) →
      ∀ U : Finset V, Fintype.card V < 2 * U.card →
        ∃ K : Finset V, K ⊆ U ∧ K.Nonempty ∧ U.card < M * K.card ∧
          2 * (coreBall U K
            (pairDistSum V / (96 * (Fintype.card V : ℝ) ^ 2))).card ≤
              Fintype.card V := by
    intro hsmall
    let δ := pairDistSum V / (48 * (Fintype.card V : ℝ) ^ 2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall' : ∀ c : V,
        2 * (Finset.univ.filter fun x : V => dist c x ≤ 12 * δ).card <
          Fintype.card V := by
      intro c
      convert hsmall c using 1
      all_goals dsimp [δ]
      all_goals ring_nf
    have htri : HasResidualTrichotomy (X := V) M δ := by
      simpa [M] using residual_vwsp_trichotomy G w hw hconn h m hh hm H hmH hfree δ hδ
    intro U hU
    obtain ⟨K, hKU, hKne, hKcard, hKball⟩ :=
      residual_trichotomy_gives_cores M (by omega) δ hδ htri hsmall' U hU
    refine ⟨K, hKU, hKne, hKcard, ?_⟩
    convert hKball using 1
    all_goals dsimp [δ]
    all_goals ring_nf
  obtain ⟨f, hf, hsum⟩ :=
    logarithmic_rabinovich_of_core_selection M hM hn hcores
  refine ⟨f, ?_, ?_⟩
  · intro u v
    exact (hf u v).trans (le_trans
      (by show G.weightedDistLight w u v ≤ G.weightedDist w u v
          letI : Nonempty (G.Walk u v) := ⟨(hconn u v).some⟩
          rw [weightedDistLight_eq_half]
          nlinarith [show 0 ≤ G.weightedDist w u v from
            le_ciInf fun p => edgeWeightSum_nonneg hw p])
      (le_rfl))
  · have hheavy : (∑ u : V, ∑ v : V, G.weightedDist w u v) =
        2 * pairDistSum V := by
      rw [← pairDistSum_heavy_eq_two_light G w hw hconn]
      rfl
    rw [hheavy]
    change pairDistSum V ≤ 32768 * Real.log (8 * (M : ℝ)) * embeddingSum f at hsum
    unfold embeddingSum at hsum
    dsimp [M]
    nlinarith

/-- The residual-carving embedding yields the corresponding logarithmic
comparison between metric spread and line spread. -/
theorem logarithmic_spread_bound_internal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (H : SimpleGraph (Fin h)) (hmH : H.edgeSet.ncard = m)
    (hfree : ¬HasInducedMinor_internal G (graphOneSubdiv H))
    (hn : 2 ≤ Fintype.card V) :
    Qspread G ≤
      (65536 * Real.log (8 * ((3 * h + m + 7 : ℕ) : ℝ))) * Qbar G := by
  have hlog : 0 < Real.log (8 * ((3 * h + m + 7 : ℕ) : ℝ)) := by
    apply Real.log_pos
    push_cast
    have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  apply sp_to_embed_bound G hconn
    (65536 * Real.log (8 * ((3 * h + m + 7 : ℕ) : ℝ))) (by positivity)
  intro w hw _
  obtain ⟨f, hf, hsum⟩ :=
    logarithmic_vwsp_embedding_internal G w hw hconn h m hh hm H hmH hfree hn
  exact ⟨f, fun u v huv => (hf u v).trans (weightedDist_le_edge hw huv), hsum⟩

end
