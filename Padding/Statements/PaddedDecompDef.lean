/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Padded Decompositions — Statement Definitions

This file defines the padded-decomposition constants that occur in theorem statements.
It deliberately contains no helper lemmas and no implementation-only definitions.

For statement verification, audit the declaration bodies listed below.  Auxiliary lemmas
about these notions, and definitions used only inside proofs, live in
`Padding/PaddedDecompDefs.lean` and the `PaddedDecomp/` implementation folder; those are
not part of the statement audit.

## Definitions

* `PaddedDecomposition.Partition`: a partition of a type, represented as a labeling function.
* `PaddedDecomposition.Partition.cluster`: the cluster (part) containing a given point.
* `PaddedDecomposition.Partition.IsBounded`: a partition is `Δ`-bounded if every cluster has
  (extended) diameter at most `Δ`.
* `PaddedDecomposition.PaddedDecomp`: a `(β, δ, Δ)`-padded decomposition of a metric space.
* `PaddedDecomposition.AdmitsPaddedDecompScheme`: a metric space admits a `(β, δ)`-padded
  decomposition scheme.

## References

* Y. Bartal, "Probabilistic approximation of metric spaces and its algorithmic applications", 1996.
* J. Fakcharoenphol, S. Rao, K. Talwar, "A tight bound on approximating arbitrary metrics
  by tree metrics", 2004.
-/

open MeasureTheory Metric Set Real

namespace PaddedDecomposition

noncomputable section

/-! ## Partitions -/

/-- A partition of a type `X`, represented as a labeling function `X → ℕ`.
Two points belong to the same cluster if and only if they receive the same label. -/
@[ext]
structure Partition (X : Type*) where
  /-- The labeling function assigning each point to a natural number label. -/
  label : X → ℕ

namespace Partition

variable {X : Type*}

instance : CoeFun (Partition X) (fun _ => X → ℕ) := ⟨Partition.label⟩

/-- The cluster (part) of partition `P` containing the point `z`. -/
def cluster (P : Partition X) (z : X) : Set X :=
  {w : X | P w = P z}

/-! ## Bounded partitions -/

/-- A partition is `Δ`-bounded if every cluster has (extended) diameter at most `Δ`.

We use `Metric.ediam` (extended non-negative real valued diameter) rather than
`Metric.diam` to correctly handle unbounded sets: `Metric.diam` maps unbounded
sets to `0`, which would make the condition vacuously true. -/
def IsBounded [PseudoMetricSpace X] (P : Partition X) (Δ : ℝ) : Prop :=
  ∀ z : X, Metric.ediam (P.cluster z) ≤ ENNReal.ofReal Δ

end Partition

/-! ## Padded Decompositions -/

universe u

/-- A `(β, δ, Δ)`-padded decomposition of a pseudo-metric space `X`.

This consists of a probability space `(Ω, μ)` together with a random partition
`partition : Ω → Partition X` satisfying:
1. **Boundedness**: Every sampled partition is `Δ`-bounded (all clusters have diameter ≤ Δ).
2. **Padding**: For every `0 ≤ γ ≤ δ` and every point `z : X`, the probability that the
   closed ball `closedBall z (γ * Δ)` is entirely contained in the cluster of `z` is at
   least `exp(-β * γ)`.

The padding property ensures that, on average, a constant fraction of the
ball around each point is "padded" — i.e., completely inside one cluster. -/
structure PaddedDecomp (X : Type u) [PseudoMetricSpace X] (β δ Δ : ℝ) where
  /-- The sample space for the random partition. -/
  Ω : Type u
  /-- Measurable space structure on the sample space. -/
  msΩ : MeasurableSpace Ω
  /-- The probability measure on the sample space. -/
  μ : @Measure Ω msΩ
  /-- The measure is a probability measure. -/
  hμ : @IsProbabilityMeasure Ω msΩ μ
  /-- The random partition: maps each sample to a partition of `X`. -/
  partition : Ω → Partition X
  /-- Every realization of the partition is `Δ`-bounded. -/
  bounded : ∀ ω, (partition ω).IsBounded Δ
  /-- For every fixed set `S` and point `z`, the event that `S` is contained in the
      sampled cluster of `z` is measurable.  In particular, this applies to every
      padding event below. -/
  cluster_subset_measurable : ∀ (S : Set X) (z : X),
    MeasurableSet {ω | S ⊆ (partition ω).cluster z}
  /-- The padding property: for `0 ≤ γ ≤ δ`, the ball `B(z, γΔ)` is likely contained
      in the cluster of `z`. -/
  padding : ∀ (γ : ℝ), 0 ≤ γ → γ ≤ δ → ∀ z : X,
    μ.toOuterMeasure {ω | Metric.closedBall z (γ * Δ) ⊆ (partition ω).cluster z} ≥
      ENNReal.ofReal (Real.exp (-β * γ))

attribute [instance] PaddedDecomp.msΩ PaddedDecomp.hμ

/-- A metric space **admits a `(β, δ)`-padded decomposition scheme** if for every `Δ > 0`,
there exists a `(β, δ, Δ)`-padded decomposition. -/
def AdmitsPaddedDecompScheme (X : Type u) [PseudoMetricSpace X] (β δ : ℝ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → Nonempty (PaddedDecomp X β δ Δ)

end

end PaddedDecomposition
