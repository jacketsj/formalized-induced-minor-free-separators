/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.RegionIntersectionDef

/-! # Region Intersection Graphs — Auxiliary Definitions

The definitions needed to **state** the region-intersection padded-decomposition theorem
(`RegionIntersectionModel`, `SimpleGraph.HasCompleteMinor`, `SimpleGraph.ExcludesMinor`)
live in `Padding/Statements/RegionIntersectionDef.lean`.  This file re-exports them
and adds the convenience predicate `IsRegionIntersectionGraphOver`, which is not needed to
state any of the headline results.
-/

open SimpleGraph Set

/-! ## Region Intersection Graph Classes -/

/-- A graph `G` is a **region intersection graph over `H`** if there exists a
region intersection model of `G` over `H`. -/
def IsRegionIntersectionGraphOver {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) : Prop :=
  Nonempty (RegionIntersectionModel G H)
