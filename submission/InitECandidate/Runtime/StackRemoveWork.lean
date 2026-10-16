import InitECandidate.Runtime.StackToLabCompose

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
/-- A conservative work budget over the actual stack evaluator's recursive sites.
Both conditional branches and return/exception continuations are included, so this
is a budget, not an assertion that unselected branches execute. The local allowance includes the bounded stack-removal bitmap copy. -/
noncomputable def removeWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  match prog with
  | .seq a b =>
      let middle := (fixClock s (StackSemEvaluate.evaluate (a, s))).2
      have lower : middle.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + removeWork a s + removeWork b middle
  | .ite _ _ _ a b => 2 + removeWork a s + removeWork b s
  | .loop body =>
      let returned := fixClock s (StackSemEvaluate.evaluate (body, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + removeWork body s +
        if contLoop returned.1 && returned.2.clock != 0 then
          removeWork (.loop body) (decClock returned.2) else 0
  | .jumpLower _ _ dest =>
      if s.clock = 0 then 2 else
        match findCode (.inl dest) s.regs s.code with
        | none => 2
        | some body => 2 + removeWork body (decClock s)
  | .rawCall dest =>
      if s.clock = 0 then 2 else
        match sptLookup dest s.code with
        | some (.seq _ body) => 2 + removeWork body (decClock s)
        | _ => 2
  | .call none dest _ =>
      if s.clock = 0 then 2 else
        match findCode dest s.regs s.code with
        | none => 2
        | some body => 2 + removeWork body (decClock s)
  | .call (some (rp, link, l1, l2)) dest handler =>
      if s.clock = 0 then 2 else
        match findCode dest (s.regs.eraseEq link) s.code with
        | none => 2
        | some body =>
            let entry := decClock (setVar link (.loc l1 l2) s)
            let middle := (fixClock entry (StackSemEvaluate.evaluate (body, entry))).2
            have lower : middle.clock ≤ entry.clock := StackSemMeasure.fixClock_clock_le entry _
            2 * (removeWork body entry + removeWork rp middle +
              match handler with
              | none => 0
              | some (hp, _, _) => removeWork hp middle) + 2
  | .storeConsts _ _ _ => 2 + (2 ^ width + 1) * s.bitmaps.length
  | _ => 2
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, StackSemStateOps.decClock, StackSemStateOps.setVar]
  all_goals omega


#print axioms removeWork
end InitECandidate.Runtime.StackRemove
