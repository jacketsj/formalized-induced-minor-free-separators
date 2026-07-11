/-
# Logarithmic Spread Bound via Rabinovich's Embedding

This file derives the alternative `O(log n)` bound on the metric spread:

  `Qspread G ≤ 1280 · log n · Qbar G`

for connected `G` with `n = |V| ≥ 2`.
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs
import InducedMinorFreeSeparators.EmbeddingTheorem
import InducedMinorFreeSeparators.VWSP
import InducedMinorFreeSeparators.PseudoRabinovich

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Rabinovich `O(log n)` spread bound.** For a connected graph `G` on `n ≥ 2`
vertices, `Qspread G ≤ 1280 · log n · Qbar G`. -/
theorem rabinovich_sp_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hV : 2 ≤ Fintype.card V) :
    Qspread G ≤ 1280 * Real.log (Fintype.card V) * Qbar G := by
  have hlogpos : 0 < Real.log (Fintype.card V) :=
    Real.log_pos (by exact_mod_cast hV)
  apply sp_to_embed_bound G hconn (1280 * Real.log (Fintype.card V)) (by positivity)
  intro w hw _hw_sum
  letI pms := vwspPMS G w hw hconn
  obtain ⟨f, hf_ne, hf_bound⟩ :=
    @PseudoRabinovich.pseudometric_rabinovich V pms _
  refine ⟨f, ?_, ?_⟩
  · intro u v hadj
    exact (hf_ne u v).trans (weightedDist_le_edge hw hadj)
  · exact hf_bound
