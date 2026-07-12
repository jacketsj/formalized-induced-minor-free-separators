/-
# Separator Theorems for Induced-Minor-Free Graphs

If `G` excludes `K_h^(1)` as an induced minor (and has at least one edge),
then `G` admits a `(2/3)`-balanced vertex separator of size
`≤ 256 h √|E| · min(1280 log n, 625 h²)`.

## Independent Verifiability

This file contains only the **statement** of the main theorem; the proof
is imported from `MainTheoremProof.lean`. To verify the statement, it
suffices to audit this file and `Defs.lean` (which defines balanced
separators, induced minors, and the 1-subdivision).
-/
import InducedMinorFreeSeparators.Defs
import InducedMinorFreeSeparators.MainTheoremProof
import InducedMinorFreeSeparators.ImprovedMainTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Main Separator Theorem.** If `G` excludes the 1-subdivision of `K_h`
as an induced minor and has at least one edge, then `G` admits a
`(2/3)`-balanced vertex separator of size at most
`256 h √|E(G)| · min(1280 log |V(G)|, 625 h²)`. -/
theorem main_separator_theorem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hm : 1 ≤ G.edgeFinset.card)
    (hIMF : ¬G.ContainsInducedMinor (oneSubdivision h)) :
    G.HasBalancedSeparator (2/3)
      (256 * (h : ℝ) * Real.sqrt (G.edgeFinset.card : ℝ) *
        min (1280 * Real.log (Fintype.card V)) (625 * (h : ℝ) ^ 2)) :=
  main_separator_theorem_proof G h hh hm hIMF

#print axioms main_separator_theorem

/-- **Improved Main Separator Theorem.** Let `H` be an arbitrary graph on
`h ≥ 2` vertices. Every positive-edge `H`-induced-minor-free graph has a
`(2/3)`-balanced separator with the logarithmic embedding loss proved by
exponential carving. The `max 1` handles the edgeless forbidden graph case. -/
theorem main_separator_theorem_arbitrary
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (H : SimpleGraph (Fin h)) [DecidableRel H.Adj]
    (hm : 1 ≤ G.edgeFinset.card)
    (hIMF : ¬G.ContainsInducedMinor H) :
    G.HasBalancedSeparator (2 / 3)
      (4 * (45 * Real.sqrt ((h : ℝ) + H.edgeFinset.card) *
        Real.sqrt (G.edgeFinset.card : ℝ) *
        (65536 * Real.log
          (8 * ((3 * h + max 1 H.edgeFinset.card + 7 : ℕ) : ℝ))))) :=
  improved_separator_theorem_all G h hh H hm hIMF

#print axioms main_separator_theorem_arbitrary
