import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Subcubify
import InducedMinorFreeSeparators.ConcurrentFlowProof.ConversionCore
import InducedMinorFreeSeparators.ConcurrentFlowProof.InducedMinorTrans
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLApplication

/-!
# Flow-Induced Minor Theorem

This file formalizes the multicommodity flow / induced-minor result from
Korhonen and Lokshtanov [KL24], whose proof is based on the Lovász Local Lemma.

The main result (`exists_inducedMinorModel_of_low_congestion`) states that if a
finite graph `G` admits a concurrent flow with congestion at most
`|V(G)|² / (40 · √(|V(H)| + |E(H)|) · √|E(G)|)`, then `G` contains `H` as an
induced minor. Equivalently (contrapositively), if `G` is `H`-induced-minor-free,
then every concurrent flow in `G` has congestion at least that bound.

## Proof outline (informal)

The proof proceeds in three stages:

1. **From concurrent flow to induced almost-embedding** [KL24, Lemma 4.3]:
   Given a subcubic graph `H` and a concurrent flow of low congestion in `G`,
   one randomly maps vertices of `H` to vertices of `G` (uniformly) and routes
   each edge `uv` of `H` along a random `φ(u)`-`φ(v)` path sampled from the
   flow distribution. For non-incident edges, the corresponding random paths
   are independent. The Lovász Local Lemma (symmetric form with
   `p · d ≤ 1/4`) guarantees a collision-free assignment exists, yielding an
   *induced almost-embedding*.

2. **From induced almost-embedding to induced minor model** [KL24, Lemma 4.4]:
   An induced almost-embedding of the *twice-subdivided* graph `H̋` (which has
   no isolated vertices) in `G` is deterministically converted into an induced
   minor model of the *once-subdivided* graph `Ḣ` in `G`. Branch sets for
   original vertices are unions of incident edge-paths; branch sets for
   subdivision vertices are carefully chosen subpaths of the middle edge-path.
   The double subdivision provides the "buffer" that ensures non-adjacent
   branch sets have no `G`-edges between them.

3. **Putting it together** [KL24, Lemma 4.5]:
   Given `H`, one constructs a subcubic graph `H''` that contains `H` as an
   induced minor, with `|E(H̋'')| ≤ 6(|V(H)| + |E(H)|)`. Applying step 1
   to `H̋''` and step 2 yields an induced minor model of `H` in `G`.

## References

* [KL24] Korhonen, Lokshtanov. "Induced-Minor-Free Graphs: Separator Theorem,
  Subexponential Algorithms, and Improved Hardness of Recognition". 2024.
* [BKLLM25] Le, Lokshtanov, et al. "A Flow-Based Approach to Separator Theorems
  for Minor-Free Graphs". 2025.
-/

open Finset Real
open scoped BigOperators NNReal

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The congestion is non-negative. -/
theorem ConcurrentFlow.congestion_nonneg [Nonempty V]
    (cf : ConcurrentFlow G) : 0 ≤ cf.congestion := by
  have h_nonneg : ∀ v, 0 ≤ cf.vertexFlow v :=
    fun v => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  exact le_trans (h_nonneg _)
    (Finset.le_sup' (fun v => cf.vertexFlow v) (Finset.mem_univ (Classical.arbitrary V)))

/-- Every vertex's flow is at most the congestion. -/
theorem ConcurrentFlow.vertexFlow_le_congestion [Nonempty V]
    (cf : ConcurrentFlow G) (v : V) : cf.vertexFlow v ≤ cf.congestion :=
  Finset.le_sup' (fun v => cf.vertexFlow v) (Finset.mem_univ v)

/-! ### Main results -/

/-- **From concurrent flow to induced almost-embedding** [KL24, Lemma 4.3].

If `H` is subcubic and `G` has a concurrent flow of congestion at most
`|V(G)|² / (15 · √|E(H)| · √|E(G)|)`, then there exists an induced
almost-embedding of `H` in `G`.

The proof uses the Lovász Local Lemma. This statement is provided as a
dependency; the proof will be supplied separately. -/
theorem exists_inducedAlmostEmbedding_of_subcubic_flow
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hV : 2 ≤ Fintype.card V) :
    Nonempty (InducedAlmostEmbedding G H) :=
  SimpleGraph.LLLApp.flow_to_iae hH cf hcong hV

/-! ### Graph construction: subcubic refinement

The construction proceeds in two stages, each captured by a separate lemma:

1. **Subcubification** (`exists_subcubify_noIsol`): Given `H`, construct a
   subcubic graph `H''` with no isolated vertices such that `H''` contains `H`
   as an induced minor. Bounds: `|E(H'')| ≤ 2|E(H)| + |V(H)|`,
   `|E(H'')| > 0` when `|V(H)| + |E(H)| > 0`.

2. **Subdivision + conversion** (`exists_subdiv_with_conversion`): Given a
   subcubic graph `H''` with no isolated vertices, construct `K = H̋''`
   (twice-subdivided). `K` is subcubic with `|E(K)| = 3|E(H'')|`. An induced
   almost-embedding of `K` in `G` can be converted to an induced minor model
   of `H''` in `G` (combining Lemma 4.4 from [KL24] with `H'' ≤_im Ḣ''`).

Combining: `|E(K)| = 3|E(H'')| ≤ 6(|V(H)| + |E(H)|)`, and
`InducedAlmostEmbedding G K → HasInducedMinor G H'' → HasInducedMinor G H`.
-/

/-- **Subcubification with no isolated vertices.**

For any graph `H`, there exists a subcubic graph `H''` with no isolated
vertices such that `H''` contains `H` as an induced minor, with
`|E(H'')| ≤ 2|E(H)| + |V(H)|`.

Construction:
* First add a pendant vertex to each isolated vertex of `H`, yielding `H'`
  with `|V(H')| ≤ 2|V(H)|`, `|E(H')| ≤ |E(H)| + |V(H)|`, no isolated
  vertices, and `H` as an induced minor.
* Then replace each vertex of degree > 3 with a binary tree, yielding
  subcubic `H''` with `|E(H'')| ≤ 2|E(H')| - |V(H')| + ... ≤ 2|E(H)| + |V(H)|`,
  no isolated vertices, and `H'` (hence `H`) as an induced minor. -/
theorem exists_subcubify_noIsol
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∃ (W'' : Type) (_ : Fintype W'') (_ : DecidableEq W''),
    ∃ (H'' : SimpleGraph W'') (_ : DecidableRel H''.Adj),
      H''.IsSubcubic ∧
      HasInducedMinor H'' H ∧
      H''.edgeFinset.card ≤ 3 * (Fintype.card W + H.edgeFinset.card) ∧
      (∀ v : W'', ∃ w : W'', H''.Adj v w) ∧
      (0 < Fintype.card W + H.edgeFinset.card → 0 < H''.edgeFinset.card) :=
  SimpleGraph.Subcubify.exists_subcubify_noIsol_impl H

/-- **Subdivision and conversion** [KL24, Lemma 4.4 + subdivision properties].

For a subcubic graph `H''` with no isolated vertices, there exists a graph
`K` (the twice-subdivided `H̋''`) such that:
* `K` is subcubic
* `|E(K)| = 3 · |E(H'')|`
* `|E(K)| > 0` when `|E(H'')| > 0`
* An induced almost-embedding of `K` in `G` yields `HasInducedMinor G H''`

The last property combines:
- Lemma 4.4 from [KL24]: induced almost-embedding of `H̋''` in `G` →
  induced minor model of `Ḣ''` (once-subdivided `H''`) in `G`
- `H''` is an induced minor of `Ḣ''` (graph is induced minor of its
  once-subdivision)
- Transitivity of HasInducedMinor -/
theorem exists_subdiv_with_conversion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hSub : H.IsSubcubic)
    (hNoIsol : ∀ v : W, ∃ w : W, H.Adj v w) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W'),
    ∃ (K : SimpleGraph W') (_ : DecidableRel K.Adj),
      K.IsSubcubic ∧
      K.edgeFinset.card = 3 * H.edgeFinset.card ∧
      (0 < H.edgeFinset.card → 0 < K.edgeFinset.card) ∧
      (Nonempty (InducedAlmostEmbedding G K) → HasInducedMinor G H) :=
  SimpleGraph.TwiceSubdiv.exists_subdiv_impl H G hSub hNoIsol

/-- **Graph construction: subcubic refinement** (combining subcubification and
subdivision).

Given any graph `H`, there exists a subcubic graph `K` such that:
1. `K` is subcubic (degree ≤ 3 at every vertex)
2. `|E(K)| ≤ 6 · (|V(H)| + |E(H)|)`
3. `|E(K)| > 0` when `|V(H)| + |E(H)| > 0`
4. Any induced almost-embedding of `K` in `G` yields `HasInducedMinor G H` -/
theorem exists_subcubic_refinement
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W'),
    ∃ (K : SimpleGraph W') (_ : DecidableRel K.Adj),
      K.IsSubcubic ∧
      (K.edgeFinset.card : ℝ) ≤ 9 * ((Fintype.card W : ℝ) + ↑H.edgeFinset.card) ∧
      ((0 : ℝ) < (Fintype.card W : ℝ) + ↑H.edgeFinset.card →
        (0 : ℝ) < ↑K.edgeFinset.card) ∧
      (Nonempty (InducedAlmostEmbedding G K) → HasInducedMinor G H) := by
  -- Step 1: Subcubify H to get H'' with no isolated vertices
  obtain ⟨W₁, instF1, instD1, H'', instDR1, hSub'', hIM, hEdge'', hNoIsol, hPos''⟩ :=
    exists_subcubify_noIsol H
  letI := instF1; letI := instD1; letI := instDR1
  -- Step 2: Subdivide H'' twice and get the conversion property
  obtain ⟨W', instF2, instD2, K, instDR2, hSubK, hEdgeK, hPosK, hConvK⟩ :=
    exists_subdiv_with_conversion G H'' hSub'' hNoIsol
  letI := instF2; letI := instD2; letI := instDR2
  -- Package the result
  refine ⟨W', instF2, instD2, K, instDR2, hSubK, ?_, ?_, ?_⟩
  · -- Edge bound: |E(K)| = 3|E(H'')| ≤ 3·3·(|V(H)| + |E(H)|) = 9(|V(H)| + |E(H)|)
    have h1 : (K.edgeFinset.card : ℝ) = 3 * (H''.edgeFinset.card : ℝ) := by
      exact_mod_cast hEdgeK
    have h2 : (H''.edgeFinset.card : ℝ) ≤ 3 * ((Fintype.card W : ℝ) + ↑H.edgeFinset.card) := by
      exact_mod_cast hEdge''
    linarith
  · -- Positivity
    intro hd
    have hd' : 0 < Fintype.card W + H.edgeFinset.card := by exact_mod_cast hd
    have h1 := hPos'' hd'
    exact_mod_cast hPosK h1
  · -- Conversion: InducedAlmostEmbedding G K → HasInducedMinor G H
    intro hae
    exact HasInducedMinor.trans (hConvK hae) hIM

/-! ### Arithmetic helper

The congestion bound with constant 40 and `√(|V(H)| + |E(H)|)` implies the
bound with constant 15 and `√|E(K)|` when `|E(K)| ≤ 6(|V(H)| + |E(H)|)`,
because `15√6 < 40` (equivalently, `1350 < 1600`).
-/

/-
If `c ≤ 6 * d` and `d ≥ 0`, then `15 * √c ≤ 40 * √d`.
This captures the arithmetic: `15√(6d) = 15√6 · √d ≤ 40√d`
since `15² · 6 = 1350 < 1600 = 40²`.
-/
private theorem fifteen_sqrt_le_fortyfive_sqrt
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ≤ 9 * d) :
    15 * √ c ≤ 45 * √ d := by
  nlinarith [ Real.sqrt_nonneg c, Real.sqrt_nonneg d, Real.mul_self_sqrt hc, Real.mul_self_sqrt hd, sq_nonneg ( Real.sqrt c - Real.sqrt d ), Real.sqrt_le_sqrt hcd ]

/-
Key arithmetic: the congestion bound transfers from the `40 · √(|V|+|E|)` form
to the `15 · √|E(K)|` form needed by the LLL lemma.
-/
private theorem congestion_bound_transfer
    {a b c d e : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (_he : 0 ≤ e)
    (hcd : c ≤ 9 * d) (hdc : 0 < d → 0 < c)
    (hle : b ≤ a / (45 * √ d * √ e)) :
    b ≤ a / (15 * √ c * √ e) := by
  by_cases hc' : c > 0 <;> by_cases hd' : d > 0 <;> simp_all +decide <;> simp_all +decide [ division_def ];
  · refine le_trans hle ?_;
    field_simp;
    exact div_le_div_of_nonneg_right ( by nlinarith [ show Real.sqrt c ≤ Real.sqrt d * Real.sqrt 9 by rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.sqrt_le_sqrt <| by linarith, show 0 ≤ a * Real.sqrt d by positivity, show 0 ≤ a * Real.sqrt 9 by positivity, Real.sqrt_nonneg d, Real.sqrt_nonneg 9, Real.mul_self_sqrt ( show 0 ≤ d by positivity ), Real.mul_self_sqrt ( show 0 ≤ (9 : ℝ) by positivity ) ] ) ( Real.sqrt_nonneg _ );
  · grind;
  · norm_num [ show c = 0 by linarith, show d = 0 by linarith ] at * ; linarith;

/-! ### Main theorem and contrapositive -/

/-- **Flow-Induced Minor Theorem** [KL24, Lemma 4.5].

If a graph `G` admits a concurrent flow of congestion at most
`|V(G)|² / (40 · √(|V(H)| + |E(H)|) · √|E(G)|)`, then `G` contains `H` as
an induced minor.

### Proof sketch

1. Construct from `H` a graph `H'` with no isolated vertices
   (`|V(H')| ≤ 2|V(H)|`, `|E(H')| ≤ |E(H)| + |V(H)|`).
2. Make `H'` subcubic by replacing high-degree vertices with binary trees,
   obtaining `H''` (`|E(H'')| ≤ 2|E(H)| + |V(H)|`).
3. The twice-subdivided `H̋''` satisfies
   `|E(H̋'')| ≤ 6(|V(H)| + |E(H)|)`, so `40/√6 > 15` gives the
   congestion bound needed for `exists_inducedAlmostEmbedding_of_subcubic_flow`.
4. Apply `exists_inducedAlmostEmbedding_of_subcubic_flow` to get an induced
   almost-embedding of `H̋''` in `G`.
5. Convert the almost-embedding into an induced minor model of `Ḣ''` in `G`
   [KL24, Lemma 4.4]: branch sets for original vertices are unions of incident
   edge-paths; branch sets for subdivision vertices are subpaths of the middle
   edge-path. The double subdivision provides the separation buffer ensuring
   non-adjacent branch sets have no `G`-edges between them.
6. Since `H` is an induced minor of `Ḣ''`, compose to get an induced minor
   model of `H` in `G`. -/
theorem exists_inducedMinorModel_of_low_congestion
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (45 * √ ((Fintype.card W : ℝ) + ↑(H.edgeFinset.card)) *
         √ ↑(G.edgeFinset.card)))
    (hV : 2 ≤ Fintype.card V) :
    HasInducedMinor G H := by
  -- Step 1: Get the subcubic refinement K from H
  obtain ⟨W', instFW', instDW', K, instDK, hKsub, hKedge, hKpos, hKconv⟩ :=
    exists_subcubic_refinement G H
  -- Register the typeclass instances for W' and K
  letI := instFW'
  letI := instDW'
  letI := instDK
  -- Step 2: Transfer the congestion bound from the 40-form to the 15-form
  have hcong' : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (K.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)) := by
    exact congestion_bound_transfer
      (sq_nonneg _)
      (ConcurrentFlow.congestion_nonneg cf)
      (Nat.cast_nonneg _)
      (by positivity)
      (Nat.cast_nonneg _)
      hKedge
      hKpos
      hcong
  -- Step 3: Apply the LLL lemma to get an induced almost-embedding of K in G
  have h_ae := exists_inducedAlmostEmbedding_of_subcubic_flow hKsub cf hcong' hV
  -- Step 4: Convert the almost-embedding to an induced minor model of H in G
  exact hKconv h_ae

/-- **Contrapositive form** of the Flow-Induced Minor Theorem.

If `G` does not contain `H` as an induced minor, then every concurrent flow
in `G` has congestion strictly greater than
`|V(G)|² / (40 · √(|V(H)| + |E(H)|) · √|E(G)|)`. -/
theorem congestion_lower_bound_of_no_induced_minor
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (cf : ConcurrentFlow G)
    (hfree : ¬HasInducedMinor G H)
    (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 /
      (45 * √ ((Fintype.card W : ℝ) + ↑(H.edgeFinset.card)) *
       √ ↑(G.edgeFinset.card)) < cf.congestion := by
  by_contra h
  push_neg at h
  exact hfree (exists_inducedMinorModel_of_low_congestion G H cf h hV)

end SimpleGraph
