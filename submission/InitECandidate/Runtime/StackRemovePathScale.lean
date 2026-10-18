import InitECandidate.Runtime.StackRemovePathWork
import InitECandidate.Runtime.StackRemoveScale
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open StackToLab

theorem selectedBranchBudget_scaled {width : Nat} [NeZero width] {C F : Type}
    (scale : Nat) (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width)
    (s : StackSemStateFiniteExact width C F) (a b a' b' : Nat)
    (first : a ≤ scale * a') (second : b ≤ scale * b') :
    selectedBranchBudget cmp reg ri s a b ≤ scale * selectedBranchBudget cmp reg ri s a' b' := by
  unfold selectedBranchBudget
  split
  · split <;> simp_all
  · simp

theorem selectedContinuationBudget_scaled {width : Nat} [NeZero width]
    (scale : Nat) (result : Option (StackSemResult width)) (l1 l2 : Nat)
    (handler : Option (HolProg width × Nat × Nat)) (r h r' h' : Nat)
    (ret : r ≤ scale * r') (hand : h ≤ scale * h') :
    selectedContinuationBudget result l1 l2 handler r h ≤
      scale * selectedContinuationBudget result l1 l2 handler r' h' := by
  unfold selectedContinuationBudget
  split
  · split <;> simp_all
  · split
    · simp
    · split <;> simp_all
  · simp

/-- The bitmap allowance is a fixed factor over the selected-path StackToLab work. -/
theorem removePathWork_scaled {width : Nat} [NeZero width] {C F : Type}
    (scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (bounded : BitmapBudget scale s) : removePathWork p s ≤ scale * pathWork p s := by
  have positive := bounded.positive
  cases p
  case seq a b =>
    have first := removePathWork_scaled scale a s bounded
    have second := removePathWork_scaled scale b _ (bounded.evaluated a)
    rw [removePathWork, pathWork]
    rcases returned : (fixClock s (StackSemEvaluate.evaluate (a, s))).1 with _ | value
    · simp only [returned, Nat.mul_add] at *
      omega
    · simp only [returned, Nat.mul_add, Nat.add_zero] at *
      omega
  case ite cmp reg ri a b =>
    have first := removePathWork_scaled scale a s bounded
    have second := removePathWork_scaled scale b s bounded
    have selected := selectedBranchBudget_scaled scale cmp reg ri s _ _ _ _ first second
    rw [removePathWork, pathWork]
    simp only [Nat.mul_add] at *
    omega
  case loop body =>
    have first := removePathWork_scaled scale body s bounded
    rw [removePathWork, pathWork]
    split_ifs with continuing
    · have rest := removePathWork_scaled scale (.loop body) _ ((bounded.evaluated body).decClock)
      simp only [Nat.mul_add] at *
      omega
    · simp only [Nat.mul_add, Nat.add_zero] at *
      omega
  case storeConsts a b c =>
    rw [removePathWork, pathWork] <;> first | simpa only [Nat.mul_comm] using bounded.leaf | simp
  case jumpLower a b dest =>
    rw [removePathWork, pathWork]
    cases ha : getVar a s with
    | none => simp only [ha]; omega
    | some va =>
      cases hb : getVar b s with
      | none => cases va <;> simp only [ha, hb] <;> omega
      | some vb =>
        cases va with
        | loc _ _ => simp only [ha, hb]; omega
        | word x =>
          cases vb with
          | loc _ _ => simp only [ha, hb]; omega
          | word y =>
            simp only [ha, hb]
            by_cases condition : wordCmpHOL .lower x y = true
            · simp only [condition, if_true]
              by_cases zero : s.clock = 0
              · simp only [zero, if_true]; omega
              · simp only [zero, if_false]
                cases found : findCode (.inl dest) s.regs s.code with
                | none => simp only; omega
                | some body =>
                  have child := removePathWork_scaled scale body (decClock s) bounded.decClock
                  simp only [Nat.mul_add] at *
                  omega
            · simp only [condition, Bool.false_eq_true, if_false]; omega
  case rawCall dest =>
    rw [removePathWork, pathWork]
    split_ifs with zero
    · omega
    · split <;> simp_all only
      · rename_i body found
        have child := removePathWork_scaled scale body (decClock s) bounded.decClock
        simp only [Nat.mul_add] at *
        omega
      · omega
  case call ret dest handler =>
    rcases ret with _ | ⟨rp,link,l1,l2⟩
    · rw [removePathWork, pathWork]
      split_ifs with zero
      · omega
      · split <;> simp_all only
        · omega
        · rename_i body found
          have child := removePathWork_scaled scale body (decClock s) bounded.decClock
          simp only [Nat.mul_add] at *
          omega
    · rw [removePathWork, pathWork]
      split_ifs with zero
      · omega
      · split <;> simp_all only
        · omega
        · rename_i body found
          have entry := (bounded.setVar link (.loc l1 l2)).decClock
          have first := removePathWork_scaled scale body _ entry
          have next := entry.evaluated body
          have second := removePathWork_scaled scale rp _ next
          cases handler with
          | none =>
            have cont := selectedContinuationBudget_scaled scale
              (fixClock (decClock (setVar link (.loc l1 l2) s))
                (StackSemEvaluate.evaluate (body, decClock (setVar link (.loc l1 l2) s)))).1 l1 l2 none _ 0 _ 0 second (by simp)
            simp only [Nat.mul_add] at *
            omega
          | some handler =>
            rcases handler with ⟨hp,hl1,hl2⟩
            have third := removePathWork_scaled scale hp _ next
            have cont := selectedContinuationBudget_scaled scale
              (fixClock (decClock (setVar link (.loc l1 l2) s))
                (StackSemEvaluate.evaluate (body, decClock (setVar link (.loc l1 l2) s)))).1 l1 l2 (some (hp,hl1,hl2)) _ _ _ _ second third
            simp only [Nat.mul_add] at *
            omega
  all_goals rw [removePathWork, pathWork] <;> first | omega | simp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock, setVar, fixClock]
  all_goals omega

#print axioms removePathWork_scaled
end InitECandidate.Runtime.StackRemove
