/-
# Peeling Argument for Balanced Separators
-/
import Mathlib
import InducedMinorFreeSeparators.ProofDefs

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Numerical helpers -/

lemma half_plus_log_three_halves_lt_one : (1 : ℝ) / 2 + Real.log (3 / 2) < 1 := by
  have := Real.log_lt_sub_one_of_pos ( show 0 < 3 / 2 by norm_num ) ; norm_num at * ; linarith

lemma one_sub_div_le_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - b / a ≤ Real.log (a / b) := by
  convert Real.log_le_sub_one_of_pos ( div_pos hb ha ) |> fun h => neg_le_neg h using 1 <;> ring_nf;
  rw [ ← Real.log_inv, inv_eq_one_div, div_eq_mul_inv ] ; ring_nf;
  norm_num [ mul_comm ]

/-! ## Graph-theoretic helpers -/

omit [Fintype V] in
lemma no_adj_across_cover (G : SimpleGraph V) {T C W : Finset V}
    (_hT : T ⊆ W) (hcover : ∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C)
    {u v : V} (hu : u ∈ T) (huC : u ∉ C) (hv : v ∈ W \ (T ∪ C))
    (hadj : G.Adj u v) : False := by
  grind +ring

omit [Fintype V] in
lemma closed_set_T_sdiff_C (G : SimpleGraph V) {T C W : Finset V}
    (_hT : T ⊆ W)
    (hcover : ∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C)
    {u w : V} (hu : u ∈ T \ C) (hadj : G.Adj u w) (hw : w ∈ W) (hwC : w ∉ C) :
    w ∈ T \ C := by
  grind +qlia

omit [Fintype V] in
lemma closed_set_W' (G : SimpleGraph V) {T C W : Finset V}
    (_hT : T ⊆ W)
    (hcover : ∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C)
    {u w : V} (hu : u ∈ W \ (T ∪ C)) (hadj : G.Adj u w) (hw : w ∈ W) (hwC : w ∉ C) :
    w ∈ W \ (T ∪ C) := by
  grind +suggestions

/-! ## Balanced separator from closed sets -/

lemma isBalancedSep_of_closed_sets (G : SimpleGraph V)
    (S : Finset V) (c : ℝ)
    (h : ∀ v : V, v ∉ S → ∃ P : Finset V, v ∈ P ∧
      (∀ u ∈ P, u ∉ S) ∧
      (↑P.card : ℝ) ≤ c * ↑(Fintype.card V) ∧
      (∀ u ∈ P, ∀ w : V, G.Adj u w → w ∉ S → w ∈ P)) :
    G.IsBalancedSeparator S c := by
  intro C
  obtain ⟨v, hv⟩ := C.exists_rep
  obtain ⟨P, hPv, hPclosed, hPsize, hPadj⟩ := h v.val v.property
  refine' le_trans _ hPsize;
  norm_cast;
  rw [ ← Set.ncard_coe_finset ];
  apply Set.ncard_le_ncard_of_injOn;
  case f => exact fun x => x.val;
  · intro w hw
    have h_reachable : SimpleGraph.Reachable (G.induce (Sᶜ : Set V)) v w := by
      simp +zetaDelta at *;
      rw [ ← hv ] at hw; exact SimpleGraph.ConnectedComponent.exact (id (Eq.symm hw));
    obtain ⟨ p ⟩ := h_reachable;
    induction p <;> simp_all +decide;
    rename_i u v w p hp ih;
    exact ih ( by
      convert hv using 1;
      exact Quot.sound ( SimpleGraph.Adj.reachable hp.symm ) ) ( by
      grind );
  · exact fun x hx y hy hxy => Subtype.ext hxy;
  · exact P.finite_toSet

/-! ## Size bound helpers -/

lemma peeling_base_size {α : ℝ} (hα : 0 < α)
    {Tc Wc n : ℕ} (hn : 2 ≤ n) (hW : 2 * n < 3 * Wc)
    (hTW : 2 * Tc ≤ Wc) (hWc : 0 < Wc)
    {Cc : ℝ} (hCc : Cc ≤ α * ↑Tc / ↑Wc) :
    Cc ≤ α * (1 / 2 + Real.log (3 * ↑Wc / (2 * ↑n))) := by
  refine le_trans hCc ?_
  rw [mul_div_assoc]; gcongr
  exact le_add_of_le_of_nonneg
    (by rw [div_le_div_iff₀] <;> norm_cast; linarith)
    (Real.log_nonneg (by rw [le_div_iff₀] <;> norm_cast <;> linarith))

lemma peeling_step_size {α : ℝ} (hα : 0 < α)
    {Wc W'c Tc n : ℕ} (hn : 2 ≤ n)
    (_hW : 2 * n < 3 * Wc) (_hW' : 2 * n < 3 * W'c)
    (_hTW : 2 * Tc ≤ Wc) (hWc : 0 < Wc) (hW'c : 0 < W'c)
    (hTle : Tc ≤ Wc - W'c) (hW'lt : W'c < Wc)
    {Cc X'c : ℝ} (hCc : Cc ≤ α * ↑Tc / ↑Wc)
    (hX'c : X'c ≤ α * (1 / 2 + Real.log (3 * ↑W'c / (2 * ↑n)))) :
    Cc + X'c ≤ α * (1 / 2 + Real.log (3 * ↑Wc / (2 * ↑n))) := by
  have h_simp : (Tc : ℝ) / Wc + Real.log (3 * W'c / (2 * n)) ≤ Real.log (3 * Wc / (2 * n)) := by
    rw [← le_sub_iff_add_le, ← Real.log_div (by positivity) (by positivity)]
    refine le_trans ?_ (one_sub_div_le_log_div (by positivity) (by positivity))
    field_simp; exact le_tsub_of_add_le_right (by norm_cast; omega)
  ring_nf at *; nlinarith

/-! ## Peeling case lemmas -/

/-
Base case of peeling: X = C, W' is small.
-/
lemma peeling_case_A (G : SimpleGraph V) (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ Fintype.card V)
    {T C W : Finset V}
    (hTW_sub : T ⊆ W) (hCW : C ⊆ W) (hTcard : 2 * T.card ≤ W.card)
    (hW : 2 * Fintype.card V < 3 * W.card)
    (hcover : ∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C)
    (hCcard : (↑C.card : ℝ) ≤ α * ↑T.card / ↑W.card)
    (hW'small : 3 * (W \ (T ∪ C)).card ≤ 2 * Fintype.card V) :
    ∃ X : Finset V, X ⊆ W ∧
      (↑X.card : ℝ) ≤ α * (1 / 2 + Real.log (3 * ↑W.card / (2 * ↑(Fintype.card V)))) ∧
      ∀ v : V, v ∈ W → v ∉ X →
        ∃ P : Finset V, v ∈ P ∧ (∀ u ∈ P, u ∈ W ∧ u ∉ X) ∧
          (↑P.card : ℝ) ≤ 2 / 3 * ↑(Fintype.card V) ∧
          (∀ u w, G.Adj u w → u ∈ P → w ∈ W → w ∉ X → w ∈ P) := by
  use C, hCW;
  refine' ⟨ _, _ ⟩;
  · convert peeling_base_size hα hn hW hTcard ( by linarith ) hCcard using 1;
  · intro v hv hvC
    by_cases hvT : v ∈ T
    · use T \ C
      refine' ⟨ Finset.mem_sdiff.mpr ⟨ hvT, hvC ⟩, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast;
        have h_card_T_minus_C : #(T \ C) ≤ #T := by
          exact Finset.card_le_card fun x hx => by aesop;
        linarith [ show #W ≤ Fintype.card V from Finset.card_le_univ W ];
      · grind +ring
    · use W \ (T ∪ C)
      refine' ⟨ _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast ; linarith;
      · grind +suggestions

/-
Inductive case of peeling: X = C ∪ X'.
-/
lemma peeling_case_B (G : SimpleGraph V) (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ Fintype.card V)
    {T C W : Finset V}
    (hTW_sub : T ⊆ W) (hCW : C ⊆ W) (hTne : T.Nonempty)
    (hTcard : 2 * T.card ≤ W.card)
    (hW : 2 * Fintype.card V < 3 * W.card)
    (hcover : ∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C)
    (hCcard : (↑C.card : ℝ) ≤ α * ↑T.card / ↑W.card)
    (hW'large : 2 * Fintype.card V < 3 * (W \ (T ∪ C)).card)
    -- IH gives X' for W' = W \ (T ∪ C)
    {X' : Finset V} (hX'sub : X' ⊆ W \ (T ∪ C))
    (hX'card : (↑X'.card : ℝ) ≤ α * (1 / 2 + Real.log
      (3 * ↑(W \ (T ∪ C)).card / (2 * ↑(Fintype.card V)))))
    (hX'bal : ∀ v : V, v ∈ W \ (T ∪ C) → v ∉ X' →
      ∃ P : Finset V, v ∈ P ∧
        (∀ u ∈ P, u ∈ W \ (T ∪ C) ∧ u ∉ X') ∧
        (↑P.card : ℝ) ≤ 2 / 3 * ↑(Fintype.card V) ∧
        (∀ u w, G.Adj u w → u ∈ P → w ∈ W \ (T ∪ C) → w ∉ X' → w ∈ P)) :
    ∃ X : Finset V, X ⊆ W ∧
      (↑X.card : ℝ) ≤ α * (1 / 2 + Real.log (3 * ↑W.card / (2 * ↑(Fintype.card V)))) ∧
      ∀ v : V, v ∈ W → v ∉ X →
        ∃ P : Finset V, v ∈ P ∧ (∀ u ∈ P, u ∈ W ∧ u ∉ X) ∧
          (↑P.card : ℝ) ≤ 2 / 3 * ↑(Fintype.card V) ∧
          (∀ u w, G.Adj u w → u ∈ P → w ∈ W → w ∉ X → w ∈ P) := by
  -- Key facts about the decomposition
  have hCX'disj : Disjoint C X' := by
    rw [Finset.disjoint_left]; intro a ha haX'
    have := hX'sub haX'; simp [Finset.mem_sdiff, Finset.mem_union] at this
    exact this.2.2 ha
  have hXsub : C ∪ X' ⊆ W :=
    Finset.union_subset hCW (hX'sub.trans Finset.sdiff_subset)
  have hW'lt : (W \ (T ∪ C)).card < W.card := by
    apply Finset.card_lt_card
    exact Finset.sdiff_ssubset (Finset.union_subset hTW_sub hCW)
      ⟨hTne.choose, Finset.mem_union_left C hTne.choose_spec⟩
  have hTle : T.card ≤ W.card - (W \ (T ∪ C)).card := by
    refine' le_tsub_of_add_le_right _;
    rw [ ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card ( Finset.union_subset hTW_sub ( Finset.sdiff_subset ) );
    · exact Finset.disjoint_left.mpr fun x hxT hxW => Finset.mem_sdiff.mp hxW |>.2 ( Finset.mem_union_left _ hxT )
  refine ⟨C ∪ X', hXsub, ?_, ?_⟩
  · -- SIZE
    rw [Finset.card_union_of_disjoint hCX'disj]; push_cast
    exact peeling_step_size hα hn hW hW'large hTcard (by omega) (by omega) hTle hW'lt hCcard hX'card
  · -- BALANCE
    intro v hv hvCX'
    have hvC : v ∉ C := fun h => hvCX' (Finset.mem_union_left X' h)
    have hvX' : v ∉ X' := fun h => hvCX' (Finset.mem_union_right C h)
    by_cases hvT : v ∈ T
    · -- v ∈ T \ C: take P = T \ C
      refine ⟨T \ C, Finset.mem_sdiff.mpr ⟨hvT, hvC⟩, ?_, ?_, ?_⟩
      · -- membership
        intro u hu
        have huT := (Finset.mem_sdiff.mp hu).1
        have huC := (Finset.mem_sdiff.mp hu).2
        refine ⟨hTW_sub huT, ?_⟩
        simp only [Finset.mem_union]; push_neg
        exact ⟨huC, fun huX' => by have := hX'sub huX'; simp [Finset.mem_sdiff, Finset.mem_union] at this; exact this.2.1 huT⟩
      · -- card: (T \ C).card ≤ T.card ≤ n/2 ≤ 2n/3
        have h1 : (T \ C).card ≤ T.card := Finset.card_le_card Finset.sdiff_subset
        have h2 : W.card ≤ Fintype.card V := Finset.card_le_univ W
        have h3 : ((T \ C).card : ℝ) ≤ T.card := Nat.cast_le.mpr h1
        have h4 : 2 * (T.card : ℝ) ≤ W.card := by exact_mod_cast hTcard
        have h5 : (W.card : ℝ) ≤ Fintype.card V := Nat.cast_le.mpr h2
        linarith
      · -- closed
        intro u w hadj hu hw hwCX'
        have hwC : w ∉ C := fun h => hwCX' (Finset.mem_union_left X' h)
        exact closed_set_T_sdiff_C G hTW_sub hcover hu hadj hw hwC
    · -- v ∉ T: v ∈ W \ (T ∪ C)
      have hv_W' : v ∈ W \ (T ∪ C) := by
        simp only [Finset.mem_sdiff, Finset.mem_union]; exact ⟨hv, by push_neg; exact ⟨hvT, hvC⟩⟩
      obtain ⟨P, hPv, hPmem, hPcard, hPclosed⟩ := hX'bal v hv_W' hvX'
      refine ⟨P, hPv, ?_, hPcard, ?_⟩
      · -- membership: ∀ u ∈ P, u ∈ W ∧ u ∉ C ∪ X'
        intro u hu
        obtain ⟨huW', huX'⟩ := hPmem u hu
        refine ⟨Finset.sdiff_subset huW', ?_⟩
        simp only [Finset.mem_union]; push_neg
        exact ⟨fun hc => absurd hc (by have := (Finset.mem_sdiff.mp huW').2; simp [Finset.mem_union] at this; exact this.2), huX'⟩
      · -- closed in W \ (C ∪ X')
        intro u w hadj hu hw hwCX'
        have hwC : w ∉ C := fun h => hwCX' (Finset.mem_union_left X' h)
        have hwX' : w ∉ X' := fun h => hwCX' (Finset.mem_union_right C h)
        -- u ∈ P implies u ∈ W \ (T ∪ C)
        have huW' := (hPmem u hu).1
        -- If w ∈ T: contradiction via cover
        by_cases hwT : w ∈ T
        · -- u ∈ W\(T∪C) so u ∉ T. G.Adj w u. By cover: w ∈ C or u ∈ C.
          have hunotT : u ∉ T := by
            have := (Finset.mem_sdiff.mp huW').2; simp [Finset.mem_union] at this; exact this.1
          have hunotC : u ∉ C := by
            have := (Finset.mem_sdiff.mp huW').2; simp [Finset.mem_union] at this; exact this.2
          have huW : u ∈ W := Finset.sdiff_subset huW'
          have := hcover w u hadj.symm hwT huW hunotT
          exact absurd (this.elim (absurd · hwC) (absurd · hunotC)) id
        · -- w ∉ T, w ∈ W, w ∉ C → w ∈ W\(T∪C)
          have hw_W' : w ∈ W \ (T ∪ C) := by
            simp only [Finset.mem_sdiff, Finset.mem_union]; exact ⟨hw, by push_neg; exact ⟨hwT, hwC⟩⟩
          exact hPclosed u w hadj hu hw_W' hwX'

/-! ## Core Peeling Construction -/

set_option maxHeartbeats 400000 in
lemma peeling_fuel (G : SimpleGraph V) (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ Fintype.card V)
    (hexp : ∀ (W : Finset V), 2 ≤ W.card →
      ∃ (T C : Finset V),
        T ⊆ W ∧ C ⊆ W ∧ T.Nonempty ∧
        2 * T.card ≤ W.card ∧
        (∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C) ∧
        (C.card : ℝ) ≤ α * T.card / W.card) :
    ∀ (fuel : ℕ) (W : Finset V), W.card ≤ fuel →
      2 * Fintype.card V < 3 * W.card →
    ∃ X : Finset V, X ⊆ W ∧
      (↑X.card : ℝ) ≤ α * (1 / 2 + Real.log (3 * ↑W.card / (2 * ↑(Fintype.card V)))) ∧
      ∀ v : V, v ∈ W → v ∉ X →
        ∃ P : Finset V, v ∈ P ∧ (∀ u ∈ P, u ∈ W ∧ u ∉ X) ∧
          (↑P.card : ℝ) ≤ 2 / 3 * ↑(Fintype.card V) ∧
          (∀ u w, G.Adj u w → u ∈ P → w ∈ W → w ∉ X → w ∈ P) := by
  intro fuel
  induction fuel with
  | zero => intro W hle hW; omega
  | succ k ih =>
    intro W hle hW
    have hW2 : 2 ≤ W.card := by omega
    obtain ⟨T, C, hTW, hCW, hTne, hTcard, hcover, hCcard⟩ := hexp W hW2
    have hW'lt : (W \ (T ∪ C)).card < W.card := by
      apply Finset.card_lt_card
      exact Finset.sdiff_ssubset (Finset.union_subset hTW hCW)
        ⟨hTne.choose, Finset.mem_union_left C hTne.choose_spec⟩
    by_cases hcase : 2 * Fintype.card V < 3 * (W \ (T ∪ C)).card
    · -- CASE B
      obtain ⟨X', hX'sub, hX'card, hX'bal⟩ := ih (W \ (T ∪ C)) (by omega) hcase
      exact peeling_case_B G α hα hn hTW hCW hTne hTcard hW hcover hCcard hcase
        hX'sub hX'card hX'bal
    · -- CASE A
      push_neg at hcase
      exact peeling_case_A G α hα hn hTW hCW hTcard hW hcover hCcard (by linarith)

lemma peeling_aux (G : SimpleGraph V) (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ Fintype.card V)
    (hexp : ∀ (W : Finset V), 2 ≤ W.card →
      ∃ (T C : Finset V),
        T ⊆ W ∧ C ⊆ W ∧ T.Nonempty ∧
        2 * T.card ≤ W.card ∧
        (∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C) ∧
        (C.card : ℝ) ≤ α * T.card / W.card)
    (W : Finset V) (hW : 2 * Fintype.card V < 3 * W.card) :
    ∃ X : Finset V, X ⊆ W ∧
      (↑X.card : ℝ) ≤ α * (1 / 2 + Real.log (3 * ↑W.card / (2 * ↑(Fintype.card V)))) ∧
      ∀ v : V, v ∈ W → v ∉ X →
        ∃ P : Finset V, v ∈ P ∧ (∀ u ∈ P, u ∈ W ∧ u ∉ X) ∧
          (↑P.card : ℝ) ≤ 2 / 3 * ↑(Fintype.card V) ∧
          (∀ u w, G.Adj u w → u ∈ P → w ∈ W → w ∉ X → w ∈ P) :=
  peeling_fuel G α hα hn hexp W.card W le_rfl hW

/-! ## Main Theorem -/

theorem expansion_to_sep (G : SimpleGraph V)
    (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ Fintype.card V)
    (hexp : ∀ (W : Finset V), 2 ≤ W.card →
      ∃ (T C : Finset V),
        T ⊆ W ∧ C ⊆ W ∧ T.Nonempty ∧
        2 * T.card ≤ W.card ∧
        (∀ u v, G.Adj u v → u ∈ T → v ∈ W → v ∉ T → u ∈ C ∨ v ∈ C) ∧
        (C.card : ℝ) ≤ α * T.card / W.card) :
    G.HasBalancedSeparator (2/3) α := by
  obtain ⟨X, hX⟩ := peeling_aux G α hα hn hexp Finset.univ ( by
    grind );
  refine' ⟨ X, _, _ ⟩;
  · refine' le_trans hX.2.1 _;
    norm_num [ mul_div_mul_comm ];
    rw [ div_self ( by positivity ), mul_one ] ; nlinarith [ half_plus_log_three_halves_lt_one ];
  · apply isBalancedSep_of_closed_sets;
    intro v hv; obtain ⟨ P, hP₁, hP₂, hP₃, hP₄ ⟩ := hX.2.2 v ( Finset.mem_univ v ) hv; use P; aesop;