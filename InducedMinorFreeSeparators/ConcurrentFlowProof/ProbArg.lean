import Mathlib
import InducedMinorFreeSeparators.ConcurrentFlowProof.Defs
import InducedMinorFreeSeparators.ConcurrentFlowProof.CombLLL
import InducedMinorFreeSeparators.ConcurrentFlowProof.ProductIndep
import InducedMinorFreeSeparators.ConcurrentFlowProof.LLLProof
import InducedMinorFreeSeparators.ConcurrentFlowProof.PathTableLLL

/-!
# LLL case proof for the concurrent flow setting
-/

open Finset SimpleGraph Real MeasureTheory Classical
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace SimpleGraph.ProbArg

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]

set_option maxHeartbeats 800000

/-! ## Existence of proper φ -/

omit [Nonempty V] [DecidableRel G.Adj] [DecidableEq W] in
private lemma exists_proper_phi (hcard : H.edgeFinset.card < Fintype.card V) :
    ∃ φ : W → V, ∀ e : H.edgeFinset, φ (e.val.out.1) ≠ φ (e.val.out.2) := by
  have h_exists_phi : (∑ b : H.edgeFinset, ∑ φ : W → V, (if φ (b.val.out.1) = φ (b.val.out.2) then 1 else 0)) < Fintype.card (W → V) := by
    have h_exists_phi : ∀ b : H.edgeFinset, (∑ φ : W → V, (if φ (b.val.out.1) = φ (b.val.out.2) then 1 else 0)) ≤ (Fintype.card V) ^ (Fintype.card W - 1) := by
      intro b
      have h_card : Finset.card (Finset.filter (fun φ : W → V => φ (b.val.out.1) = φ (b.val.out.2)) Finset.univ) ≤ Fintype.card V ^ (Fintype.card W - 1) := by
        have h_card : Finset.card (Finset.image (fun φ : W → V => fun w : {w : W // w ≠ (b.val.out.1)} => φ w.val) (Finset.filter (fun φ : W → V => φ (b.val.out.1) = φ (b.val.out.2)) Finset.univ)) ≤ Fintype.card V ^ (Fintype.card W - 1) := by
          refine' le_trans ( Finset.card_le_univ _ ) _;
          simp +decide [ Fintype.card_subtype_compl ];
        rwa [ Finset.card_image_of_injOn ] at h_card;
        intro φ₁ hφ₁ φ₂ hφ₂ h_eq; ext w; by_cases hw : w = (b.val.out.1) <;> simp_all +decide [ funext_iff ] ;
        have := Quot.out_eq ( b : Sym2 W ) ; rcases h : Quot.out ( b : Sym2 W ) with ⟨ x, y ⟩ ; aesop;
      aesop;
    refine' lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => h_exists_phi _ ) _ ; simp +decide [ Finset.card_univ ];
    rcases k : Fintype.card W with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
    · rw [ Fintype.card_eq_zero_iff ] at k ; aesop_cat;
    · exact mul_lt_mul_of_pos_right hcard ( pow_pos ( Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt hcard ) ) ⟩ ) _ );
  contrapose! h_exists_phi;
  rw [ Finset.sum_comm ];
  exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun φ _ => show ∑ e : H.edgeFinset, ( if φ ( Quot.out e.val ).1 = φ ( Quot.out e.val ).2 then 1 else 0 ) ≥ 1 from by obtain ⟨ e, he ⟩ := h_exists_phi φ; exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun e _ => by positivity ) ( Finset.mem_univ e ) ) )

/-! ## Existence of paths -/

omit [Nonempty V] [DecidableRel G.Adj] in
private lemma exists_path_between (cf : ConcurrentFlow G) (a b : V) (hab : a ≠ b) :
    ∃ l ∈ cf.support, l.head? = some a ∧ l.getLast? = some b := by
  have htf := cf.total_flow a b hab
  by_contra h; push_neg at h
  have : (∑ l ∈ cf.support.filter (fun l => l.head? = some a ∧ l.getLast? = some b),
    (cf.flow l : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl; simp only [Finset.mem_filter] at hl
    exact absurd hl.2.2 (h l hl.1 hl.2.1)
  linarith

/-! ## Main theorem -/

theorem lll_main
    (hH : H.IsSubcubic)
    (cf : ConcurrentFlow G)
    (hcong : cf.congestion ≤
      (Fintype.card V : ℝ) ^ 2 /
        (15 * √ (H.edgeFinset.card : ℝ) * √ (G.edgeFinset.card : ℝ)))
    (hEH : 1 < H.edgeFinset.card)
    (hV : 2 ≤ Fintype.card V)
    (hn : 1796 < Fintype.card V)
    (h100 : 100 * H.edgeFinset.card < Fintype.card V) :
    ∃ (φ : W → V) (pathChoice : H.edgeFinset → List V),
      (∀ e : H.edgeFinset, pathChoice e ∈ cf.support) ∧
      (∀ e : H.edgeFinset,
        (pathChoice e).head? = some (φ (e.val.out.1)) ∧
        (pathChoice e).getLast? = some (φ (e.val.out.2))) ∧
      (∀ e₁ e₂ : H.edgeFinset, e₁ ≠ e₂ →
        (e₁.val.out.1 ≠ e₂.val.out.1) → (e₁.val.out.1 ≠ e₂.val.out.2) →
        (e₁.val.out.2 ≠ e₂.val.out.1) → (e₁.val.out.2 ≠ e₂.val.out.2) →
        MutuallyInducedPaths G (pathChoice e₁) (pathChoice e₂)) := by
  exact PathTableLLL.path_table_lll hH cf hcong hEH hV hn h100

end SimpleGraph.ProbArg
end
