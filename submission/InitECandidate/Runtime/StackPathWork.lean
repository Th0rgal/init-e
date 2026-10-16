import InitECandidate.Runtime.StackToLabLoop
import InitECandidate.Runtime.StackSelectedBranchBudget
import InitECandidate.Runtime.StackSelectedCallBudget

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- Work budget that charges only a selected conditional branch and only a
reached sequence suffix. Returning calls charge only a valid reached continuation, with the existing factor-two overhead. -/
noncomputable def pathWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  match prog with
  | .seq a b =>
      let returned := fixClock s (StackSemEvaluate.evaluate (a, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + pathWork a s + match returned.1 with
        | none => pathWork b returned.2
        | _ => 0
  | .ite cmp reg ri a b => 2 + selectedBranchBudget cmp reg ri s (pathWork a s) (pathWork b s)
  | .loop body =>
      let returned := fixClock s (StackSemEvaluate.evaluate (body, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + pathWork body s +
        if contLoop returned.1 && returned.2.clock != 0 then
          pathWork (.loop body) (decClock returned.2) else 0
  | .jumpLower _ _ dest =>
      if s.clock = 0 then 2 else
        match findCode (.inl dest) s.regs s.code with
        | none => 2
        | some body => 2 + pathWork body (decClock s)
  | .rawCall dest =>
      if s.clock = 0 then 2 else
        match sptLookup dest s.code with
        | some (.seq _ body) => 2 + pathWork body (decClock s)
        | _ => 2
  | .call none dest _ =>
      if s.clock = 0 then 2 else
        match findCode dest s.regs s.code with
        | none => 2
        | some body => 2 + pathWork body (decClock s)
  | .call (some (rp, link, l1, l2)) dest handler =>
      if s.clock = 0 then 2 else
        match findCode dest (s.regs.eraseEq link) s.code with
        | none => 2
        | some body =>
            let entry := decClock (setVar link (.loc l1 l2) s)
            let middle := (fixClock entry (StackSemEvaluate.evaluate (body, entry))).2
            have lower : middle.clock ≤ entry.clock := StackSemMeasure.fixClock_clock_le entry _
            2 * (pathWork body entry + selectedContinuationBudget
              (fixClock entry (StackSemEvaluate.evaluate (body, entry))).1 l1 l2 handler
              (pathWork rp middle)
              (match (generalizing := false) handler with
              | none => 0
              | some (hp, _, _) => pathWork hp middle)) + 2
  | _ => 2
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, StackSemStateOps.decClock, StackSemStateOps.setVar]
  all_goals omega

theorem two_le_pathWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : 2 ≤ pathWork prog s := by
  cases prog
  case call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩ <;> rw [pathWork]
    all_goals repeat first | omega | simp | split
  all_goals rw [pathWork]
  all_goals repeat first | omega | simp | split


#print axioms pathWork
end InitECandidate.Runtime.StackToLab
