/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.MuModel

/-! # Intersection graphs of families of connected sets

The auxiliary graphs `G'_{i,j}` in the region-intersection asymptotic-dimension proof are all
of one form: take a family of nonempty connected subsets of `V(H)` indexed by some vertex set
`W`, and build the graph on `W` whose edges are exactly the intersecting pairs.  This file
packages that construction and shows it is always a `RegionIntersectionModel` over `H`.
-/

open SimpleGraph Set

/-- The **intersection graph** of a family `R : W → Set V₂`: vertices `u ≠ v` are adjacent iff
their sets `R u`, `R v` intersect. -/
def intersectionGraph {W V₂ : Type*} (R : W → Set V₂) : SimpleGraph W where
  Adj u v := u ≠ v ∧ (R u ∩ R v).Nonempty
  symm := by
    rintro u v ⟨hne, x, hx⟩
    exact ⟨hne.symm, x, hx.2, hx.1⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
lemma intersectionGraph_adj {W V₂ : Type*} (R : W → Set V₂) (u v : W) :
    (intersectionGraph R).Adj u v ↔ u ≠ v ∧ (R u ∩ R v).Nonempty := Iff.rfl

/-- The canonical region intersection model of the intersection graph of a family of
nonempty connected sets. -/
def intersectionModel {W V₂ : Type*} (H : SimpleGraph V₂) (R : W → Set V₂)
    (hne : ∀ w, (R w).Nonempty)
    (hconn : ∀ w, ∀ a b : V₂, a ∈ R w → b ∈ R w →
      ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ R w) :
    RegionIntersectionModel (intersectionGraph R) H where
  region := R
  region_nonempty := hne
  region_connected := hconn
  adj_intersect := by
    rintro u v ⟨_, hx⟩
    exact hx
  nonadj_disjoint := by
    intro u v hne hadj
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra h
    exact hadj ⟨hne, Set.nonempty_iff_ne_empty.mpr h⟩

@[simp]
lemma intersectionModel_region {W V₂ : Type*} (H : SimpleGraph V₂) (R : W → Set V₂)
    (hne : ∀ w, (R w).Nonempty)
    (hconn : ∀ w, ∀ a b : V₂, a ∈ R w → b ∈ R w →
      ∃ (p : H.Walk a b), ∀ x ∈ p.support, x ∈ R w) (w : W) :
    (intersectionModel H R hne hconn).region w = R w := rfl
