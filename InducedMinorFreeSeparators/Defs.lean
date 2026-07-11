/-
# Statement-Level Definitions for the Main Separator Theorem

This file contains **only** the definitions that appear in the *statement*
of the main result (`main_separator_theorem` in `MainTheorem.lean`):

  If G excludes K_h^(1) as an induced minor (and has at least one edge),
  then G admits a (2/3)-balanced vertex separator of size ≤ 160000 h³ √|E|.

## Definitions

* `SimpleGraph.IsBalancedSeparator` — a set S is a c-balanced vertex separator
* `SimpleGraph.HasBalancedSeparator` — G admits a c-balanced separator of size ≤ k
* `SimpleGraph.ContainsInducedMinor` — G contains H as an induced minor
* `oneSubdivision` — the 1-subdivision of the complete graph K_h

No LP formulations, metric spreads, or proof-internal machinery is included here.
Those live in `ProofDefs.lean`, which imports this file.

To verify the main theorem statement independently, it suffices to audit
this file and `MainTheorem.lean`.
-/
import Mathlib

variable {V : Type*}

/-! ## Balanced Vertex Separators -/

/-- A set `S` of vertices is a `c`-balanced vertex separator of `G` if every
connected component of the induced subgraph `G[Vᶜ_S]` (i.e., `G` restricted
to vertices not in `S`) has at most `c * |V|` vertices. -/
def SimpleGraph.IsBalancedSeparator [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (c : ℝ) : Prop :=
  ∀ C : (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent,
    (C.supp.ncard : ℝ) ≤ c * Fintype.card V

/-- A graph `G` admits a `c`-balanced vertex separator of size at most `k`. -/
def SimpleGraph.HasBalancedSeparator [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℝ) (k : ℝ) : Prop :=
  ∃ S : Finset V, (S.card : ℝ) ≤ k ∧ G.IsBalancedSeparator S c

/-! ## Induced Minors and 1-Subdivision -/

/-- A graph G contains H as an induced minor. -/
def SimpleGraph.ContainsInducedMinor {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ (φ : W → Set V),
    (∀ w, (φ w).Nonempty) ∧
    (∀ w, (G.induce (φ w)).Connected) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (φ w₁) (φ w₂)) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ v₁ ∈ φ w₁, ∃ v₂ ∈ φ w₂, G.Adj v₁ v₂) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → ¬H.Adj w₁ w₂ →
      ∀ v₁ ∈ φ w₁, ∀ v₂ ∈ φ w₂, ¬G.Adj v₁ v₂)

/-- Edge vertices of K_h. -/
abbrev KEdge (h : ℕ) := {p : Fin h × Fin h // p.1 < p.2}

/-- Vertex type of K_h^(1) (a sum type). -/
abbrev SubdivVertex (h : ℕ) := Fin h ⊕ KEdge h

private def subdivAdj (h : ℕ) (v w : SubdivVertex h) : Prop :=
  match v, w with
  | .inl i, .inr ⟨(a, b), _⟩ => i = a ∨ i = b
  | .inr ⟨(a, b), _⟩, .inl i => i = a ∨ i = b
  | _, _ => False

private lemma subdivAdj_symm (h : ℕ) : Symmetric (subdivAdj h) := by
  intro v w; unfold subdivAdj; cases v <;> cases w <;> simp_all

private lemma subdivAdj_irrefl (h : ℕ) : Std.Irrefl (subdivAdj h) :=
  ⟨fun v => by match v with
    | .inl _ => simp [subdivAdj]
    | .inr _ => simp [subdivAdj]⟩

/-- The 1-subdivision of the complete graph K_h. -/
def oneSubdivision (h : ℕ) : SimpleGraph (SubdivVertex h) :=
  ⟨subdivAdj h, subdivAdj_symm h, subdivAdj_irrefl h⟩

/-- Decidable adjacency for oneSubdivision. -/
noncomputable instance oneSubdivision_decRel (h : ℕ) : DecidableRel (oneSubdivision h).Adj :=
  Classical.decRel _
