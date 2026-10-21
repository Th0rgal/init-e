import InitECandidate.Runtime.StackToLabLoop
import InitECandidate.Runtime.StackSelectedBranchBudget
import InitECandidate.Runtime.StackSelectedCallBudget

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- Price-parametric cost of the actual Stack execution tree. Structural nodes
can be free. Only the reached suffix/branch, dynamic loop iteration, callee,
and valid return/exception continuation contribute recursive work. RawCall
enters the body after the prologue. This definition is not itself a native
instruction bound: each local price must be justified by compiler transfer. -/
noncomputable def stackExecutionCost {width : Nat} [NeZero width] {C F : Type}
    (price : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  match prog with
  | .seq a b =>
      let returned := fixClock s (StackSemEvaluate.evaluate (a, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      price prog s + stackExecutionCost price a s + match returned.1 with
        | none => stackExecutionCost price b returned.2
        | _ => 0
  | .ite cmp reg ri a b => price prog s + selectedBranchBudget cmp reg ri s (stackExecutionCost price a s) (stackExecutionCost price b s)
  | .loop body =>
      let returned := fixClock s (StackSemEvaluate.evaluate (body, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      price prog s + stackExecutionCost price body s +
        if contLoop returned.1 && returned.2.clock != 0 then
          stackExecutionCost price (.loop body) (decClock returned.2) else 0
  | .jumpLower r1 r2 dest =>
      match StackSemStateOps.getVar r1 s, StackSemStateOps.getVar r2 s with
      | some (.word x), some (.word y) =>
        if wordCmpHOL .lower x y then
          if s.clock = 0 then price prog s else
            match findCode (.inl dest) s.regs s.code with
            | none => price prog s
            | some body => price prog s + stackExecutionCost price body (decClock s)
        else price prog s
      | _, _ => price prog s
  | .rawCall dest =>
      if s.clock = 0 then price prog s else
        match sptLookup dest s.code with
        | some (.seq _ body) => price prog s + stackExecutionCost price body (decClock s)
        | _ => price prog s
  | .call none dest handler =>
      if handler.isSome then price prog s else
      if s.clock = 0 then price prog s else
        match findCode dest s.regs s.code with
        | none => price prog s
        | some body => price prog s + stackExecutionCost price body (decClock s)
  | .call (some (rp, link, l1, l2)) dest handler =>
      if s.clock = 0 then price prog s else
        match findCode dest (s.regs.eraseEq link) s.code with
        | none => price prog s
        | some body =>
            let entry := decClock (setVar link (.loc l1 l2) s)
            let middle := (fixClock entry (StackSemEvaluate.evaluate (body, entry))).2
            have lower : middle.clock ≤ entry.clock := StackSemMeasure.fixClock_clock_le entry _
            stackExecutionCost price body entry + selectedContinuationBudget
              (fixClock entry (StackSemEvaluate.evaluate (body, entry))).1 l1 l2 handler
              (stackExecutionCost price rp middle)
              (match (generalizing := false) handler with
              | none => 0
              | some (hp, _, _) => stackExecutionCost price hp middle) + price prog s
  | _ => price prog s
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, StackSemStateOps.decClock, StackSemStateOps.setVar]
  all_goals omega

#print axioms stackExecutionCost
end InitECandidate.Runtime.StackToLab
