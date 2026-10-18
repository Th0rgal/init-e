import InitECandidate.Runtime.StackPathWork

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open StackToLab

/-- Stack-removal work along the actually selected path: the same selected
branch, reached sequence suffix and reached-continuation shape as the StackToLab
path budget, with the bounded bitmap-copy allowance charged at storeConsts. -/
noncomputable def removePathWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  match prog with
  | .seq a b =>
      let returned := fixClock s (StackSemEvaluate.evaluate (a, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + removePathWork a s + match returned.1 with
        | none => removePathWork b returned.2
        | _ => 0
  | .ite cmp reg ri a b => 2 + selectedBranchBudget cmp reg ri s (removePathWork a s) (removePathWork b s)
  | .loop body =>
      let returned := fixClock s (StackSemEvaluate.evaluate (body, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + removePathWork body s +
        if contLoop returned.1 && returned.2.clock != 0 then
          removePathWork (.loop body) (decClock returned.2) else 0
  | .jumpLower r1 r2 dest =>
      match StackSemStateOps.getVar r1 s, StackSemStateOps.getVar r2 s with
      | some (.word x), some (.word y) =>
        if wordCmpHOL .lower x y then
          if s.clock = 0 then 2 else
            match findCode (.inl dest) s.regs s.code with
            | none => 2
            | some body => 2 + removePathWork body (decClock s)
        else 2
      | _, _ => 2
  | .rawCall dest =>
      if s.clock = 0 then 2 else
        match sptLookup dest s.code with
        | some (.seq _ body) => 2 + removePathWork body (decClock s)
        | _ => 2
  | .call none dest _ =>
      if s.clock = 0 then 2 else
        match findCode dest s.regs s.code with
        | none => 2
        | some body => 2 + removePathWork body (decClock s)
  | .call (some (rp, link, l1, l2)) dest handler =>
      if s.clock = 0 then 2 else
        match findCode dest (s.regs.eraseEq link) s.code with
        | none => 2
        | some body =>
            let entry := decClock (setVar link (.loc l1 l2) s)
            let middle := (fixClock entry (StackSemEvaluate.evaluate (body, entry))).2
            have lower : middle.clock ≤ entry.clock := StackSemMeasure.fixClock_clock_le entry _
            removePathWork body entry + selectedContinuationBudget
              (fixClock entry (StackSemEvaluate.evaluate (body, entry))).1 l1 l2 handler
              (removePathWork rp middle)
              (match (generalizing := false) handler with
              | none => 0
              | some (hp, _, _) => removePathWork hp middle) + 2
  | .storeConsts _ _ _ => 2 + (2 ^ width + 1) * s.bitmaps.length
  | _ => 2
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, StackSemStateOps.decClock, StackSemStateOps.setVar]
  all_goals omega


#print axioms removePathWork
end InitECandidate.Runtime.StackRemove
