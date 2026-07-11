import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs

/-!
# Bridge Lemma
-/

open Finset SimpleGraph List
open scoped BigOperators

noncomputable section

namespace SimpleGraph.BridgeLemma

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-
Helper: max index in A exists
-/
omit [Fintype V] in
lemma exists_maxA_idx {l : List V} {A B : Finset V} (hl : 2 ≤ l.length)
    (hA : l.get ⟨0, by omega⟩ ∈ A) (hB : l.get ⟨l.length - 1, by omega⟩ ∈ B)
    (hAB_disj : Disjoint A B) :
    ∃ (lastA : ℕ) (hlA : lastA < l.length),
      lastA + 1 < l.length ∧
      l.get ⟨lastA, hlA⟩ ∈ A ∧
      (∀ k (hk : k < l.length), l.get ⟨k, hk⟩ ∈ A → k ≤ lastA) := by
  by_contra! h
  generalize_proofs at *;
  -- By repeatedly applying the hypothesis `h`, we can find an index `lastA` such that `lastA + 1 < l.length` and `l.get ⟨lastA, by sorry⟩ ∈ A`.
  have h_seq : ∀ n : ℕ, ∃ lastA : ℕ, lastA < l.length ∧ lastA + 1 < l.length ∧ l.get ⟨lastA, by
    induction' n with n ih <;> simp_all +decide [ Finset.disjoint_left ];
    -- Apply the hypothesis `h` to the last element of the list.
    obtain ⟨k, hk⟩ := h 0 (by linarith) (by linarith) hA;
    obtain ⟨ ⟨ hk₁, hk₂ ⟩, hk₃ ⟩ := hk;
    induction' n : l.length - k using Nat.strong_induction_on with n ih generalizing k;
    grind⟩ ∈ A ∧ n ≤ lastA := by
    grind
  generalize_proofs at *;
  exact absurd ( ‹∀ n lastA : ℕ, lastA < l.length› ( l.length ) ( l.length ) ) ( by simp +decide )

/-
Helper: min index in B after lastA exists and is ≥ lastA + 2
-/
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma exists_firstB_idx {l : List V} {A B : Finset V} (hl : 2 ≤ l.length)
    (hl_chain : l.IsChain G.Adj)
    (hAB_nonadj : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b)
    {lastA : ℕ} (hlA : lastA < l.length) (hlA1 : lastA + 1 < l.length)
    (hlA_mem : l.get ⟨lastA, hlA⟩ ∈ A)
    (_hlA_max : ∀ k (hk : k < l.length), l.get ⟨k, hk⟩ ∈ A → k ≤ lastA)
    (hB : l.get ⟨l.length - 1, by omega⟩ ∈ B) :
    ∃ (firstB : ℕ) (hfB : firstB < l.length),
      l.get ⟨firstB, hfB⟩ ∈ B ∧
      lastA + 2 ≤ firstB ∧
      (∀ k (hk : k < l.length), lastA < k → l.get ⟨k, hk⟩ ∈ B → firstB ≤ k) := by
  -- Since $l$ is a chain, $l [lastA]$ and $l[lastA + 1]$ are adjacent in $G$.
  have h_adj : G.Adj (l.get ⟨lastA, hlA⟩) (l.get ⟨lastA + 1, by linarith⟩) := by
    rw [ List.isChain_iff_getElem ] at hl_chain;
    exact hl_chain lastA hlA1;
  -- By repeatedly applying hAB_nonadj, we can find an index firstB such that l.get ⟨firstB, hfB⟩ ∈ B and lastA + 2 ≤ firstB.
  have h_exists_firstB : ∃ firstB, ∃ (hfB : firstB < l.length), l.get ⟨firstB, hfB⟩ ∈ B ∧ lastA + 2 ≤ firstB := by
    grind +splitImp;
  contrapose! h_exists_firstB;
  intro firstB hfB hB_firstB
  induction' firstB using Nat.strong_induction_on with firstB ih;
  grind

/-
Helper: the bridge set is connected
-/
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma bridge_connected {l : List V} (hl_chain : l.IsChain G.Adj) (_hl_nodup : l.Nodup)
    {lo hi : ℕ} (hgap : lo + 2 ≤ hi) (hhi : hi < l.length) :
    (G.induce { v | ∃ (k : ℕ) (hk : k < l.length),
      lo < k ∧ k < hi ∧ l.get ⟨k, hk⟩ = v }).Connected := by
  refine' SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨ ⟨ _, ⟨ lo + 1, _, _, _, rfl ⟩ ⟩, _ ⟩;
  grind +locals;
  grind +locals;
  lia;
  rintro ⟨ v, ⟨ k, hk, hk', hk'', rfl ⟩ ⟩;
  induction' k with k ih;
  · contradiction;
  · rcases eq_or_lt_of_le ( Nat.le_of_lt_succ hk' ) with rfl | hk' <;> simp_all +decide [ List.isChain_iff_getElem ];
    refine' SimpleGraph.Reachable.trans ( ih ( by linarith ) ( by linarith ) ) _;
    exact SimpleGraph.Adj.reachable ( hl_chain k (by omega) )

omit [Fintype V] [DecidableRel G.Adj] in
/-- The **Bridge Lemma**. -/
theorem bridge_exists
    (l : List V) (hl : 2 ≤ l.length)
    (hl_chain : l.IsChain G.Adj) (hl_nodup : l.Nodup)
    (A B : Finset V)
    (hA : l.get ⟨0, by omega⟩ ∈ A) (hB : l.get ⟨l.length - 1, by omega⟩ ∈ B)
    (hAB_disj : Disjoint A B)
    (hAB_nonadj : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    ∃ (S : Set V),
      Set.Nonempty S ∧
      (∀ v ∈ S, v ∈ (l.toFinset : Set V)) ∧
      (∀ v ∈ S, v ∉ A) ∧ (∀ v ∈ S, v ∉ B) ∧
      (G.induce S).Connected ∧
      (∃ a s, a ∈ A ∧ s ∈ S ∧ G.Adj a s) ∧
      (∃ b s, b ∈ B ∧ s ∈ S ∧ G.Adj s b) := by
  obtain ⟨lastA, hlA, hlA1, hlA_mem, hlA_max⟩ :=
    exists_maxA_idx hl hA hB hAB_disj
  obtain ⟨firstB, hfB, hfB_mem, hgap, hfB_min⟩ :=
    exists_firstB_idx hl hl_chain hAB_nonadj hlA hlA1 hlA_mem hlA_max hB
  set S : Set V := { v | ∃ (k : ℕ) (hk : k < l.length),
    lastA < k ∧ k < firstB ∧ l.get ⟨k, hk⟩ = v }
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Nonempty
    exact ⟨l.get ⟨lastA + 1, by omega⟩, lastA + 1, by omega, by omega, by omega, rfl⟩
  · -- In l.toFinset
    rintro v ⟨k, hk, -, -, rfl⟩
    simp
  · -- Not in A
    rintro v ⟨k, hk, hk1, -, rfl⟩
    intro hmem
    exact absurd (hlA_max k hk hmem) (by omega)
  · -- Not in B
    rintro v ⟨k, hk, hk1, hk2, rfl⟩
    intro hmem
    exact absurd (hfB_min k hk (by omega) hmem) (by omega)
  · -- Connected
    exact bridge_connected hl_chain hl_nodup hgap hfB
  · -- Adjacent to A: lastA is in A, lastA+1 is in S, and they are adjacent
    have hadj : G.Adj (l.get ⟨lastA, hlA⟩) (l.get ⟨lastA + 1, hlA1⟩) :=
      hl_chain.getElem lastA hlA1
    exact ⟨l.get ⟨lastA, hlA⟩, l.get ⟨lastA + 1, hlA1⟩, hlA_mem,
           ⟨lastA + 1, hlA1, by omega, by omega, rfl⟩, hadj⟩
  · -- Adjacent to B: firstB is in B, firstB-1 is in S, and they are adjacent
    have hadj : G.Adj (l.get ⟨firstB - 1, by omega⟩) (l.get ⟨firstB, hfB⟩) := by
      have h := hl_chain.getElem (firstB - 1) (by omega : firstB - 1 + 1 < l.length)
      simp only [show firstB - 1 + 1 = firstB by omega] at h
      exact h
    exact ⟨l.get ⟨firstB, hfB⟩, l.get ⟨firstB - 1, by omega⟩, hfB_mem,
           ⟨firstB - 1, by omega, by omega, by omega, rfl⟩, hadj⟩

end SimpleGraph.BridgeLemma
end
