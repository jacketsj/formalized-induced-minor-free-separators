/-
# Induced Minor Model

Definitions of induced minor models and the induced minor relation for simple graphs.
-/
import Mathlib

/-! ### Induced minor model -/
structure InducedMinorModel {V : Type*} {W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Set V
  branch_connected : ∀ w, (G.induce (branch w)).Connected
  branch_disjoint : ∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (branch w₁) (branch w₂)
  adj_preserved : ∀ w₁ w₂, H.Adj w₁ w₂ →
    ∃ v₁ ∈ branch w₁, ∃ v₂ ∈ branch w₂, G.Adj v₁ v₂
  nonadj_preserved : ∀ w₁ w₂, w₁ ≠ w₂ → ¬H.Adj w₁ w₂ →
    ∀ v₁ ∈ branch w₁, ∀ v₂ ∈ branch w₂, ¬G.Adj v₁ v₂

def HasInducedMinor {V : Type*} {W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (InducedMinorModel G H)
