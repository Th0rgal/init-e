import InitECandidate.Runtime.StackToLabLoop
import InitECandidate.Runtime.StackToLabIf

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- A conservative work budget over the actual stack evaluator's recursive sites.
Both conditional branches and return/exception continuations are included, so this
is a budget, not an assertion that unselected branches execute. The two-unit local
allowance covers the label compiler's control instructions. -/
noncomputable def stackWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  match prog with
  | .seq a b =>
      let middle := (fixClock s (StackSemEvaluate.evaluate (a, s))).2
      have lower : middle.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + stackWork a s + stackWork b middle
  | .ite _ _ _ a b => 2 + stackWork a s + stackWork b s
  | .loop body =>
      let returned := fixClock s (StackSemEvaluate.evaluate (body, s))
      have lower : returned.2.clock ≤ s.clock := StackSemMeasure.fixClock_clock_le s _
      2 + stackWork body s +
        if contLoop returned.1 && returned.2.clock != 0 then
          stackWork (.loop body) (decClock returned.2) else 0
  | .jumpLower _ _ dest =>
      if s.clock = 0 then 2 else
        match findCode (.inl dest) s.regs s.code with
        | none => 2
        | some body => 2 + stackWork body (decClock s)
  | .rawCall dest =>
      if s.clock = 0 then 2 else
        match sptLookup dest s.code with
        | some (.seq _ body) => 2 + stackWork body (decClock s)
        | _ => 2
  | .call none dest _ =>
      if s.clock = 0 then 2 else
        match findCode dest s.regs s.code with
        | none => 2
        | some body => 2 + stackWork body (decClock s)
  | .call (some (rp, link, l1, l2)) dest handler =>
      if s.clock = 0 then 2 else
        match findCode dest (s.regs.eraseEq link) s.code with
        | none => 2
        | some body =>
            let entry := decClock (setVar link (.loc l1 l2) s)
            let middle := (fixClock entry (StackSemEvaluate.evaluate (body, entry))).2
            have lower : middle.clock ≤ entry.clock := StackSemMeasure.fixClock_clock_le entry _
            2 + stackWork body entry + stackWork rp middle +
              match handler with
              | none => 0
              | some (hp, _, _) => stackWork hp middle
  | _ => 2
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, StackSemStateOps.decClock, StackSemStateOps.setVar]
  all_goals omega

theorem two_le_stackWork {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) : 2 ≤ stackWork prog s := by
  cases prog
  case call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩ <;> rw [stackWork]
    all_goals repeat first | omega | simp | split
  all_goals rw [stackWork]
  all_goals repeat first | omega | simp | split

/-- Sequence composition at a concrete source-derived budget. -/
theorem stackWork_seq_bound {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp a s (stackWork a s))
    (second : ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (a, s) = (none, middle) →
      BoundedFlattenProp b middle (stackWork b middle)) :
    BoundedFlattenProp (.seq a b) s (stackWork (.seq a b) s) := by
  let middle := (StackSemEvaluate.evaluate (a, s)).2
  have next : ∀ (reached : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (a, s) = (none, reached) →
      BoundedFlattenProp b reached (stackWork b middle) := by
    intro reached run
    have eq : middle = reached := by simp [middle, run]
    rw [eq]
    exact second reached run
  have composed := flattenSeq_reached_bounded s a b (stackWork a s) (stackWork b middle) first next
  intro t r final n l cs bs target hyps
  apply boundedFlattenConcl_mono (a := stackWork a s + stackWork b middle) _
    (composed t r final n l cs bs target hyps)
  rw [stackWork, StackSemEvaluateClock.fixClockEvaluate]
  change stackWork a s + stackWork b middle ≤ 2 + stackWork a s + stackWork b middle
  omega

/-- Loop composition uses the work budget at its actual recursive successor. -/
theorem stackWork_loop_bound {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp body s (stackWork body s))
    (next : ∀ (result : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (body, s) = (result, middle) →
      contLoop result = true → middle.clock ≠ 0 →
      BoundedFlattenProp (.loop body) (decClock middle) (stackWork (.loop body) (decClock middle))) :
    BoundedFlattenProp (.loop body) s (stackWork (.loop body) s) := by
  let returned := StackSemEvaluate.evaluate (body, s)
  let rest := if contLoop returned.1 && returned.2.clock != 0 then
      stackWork (.loop body) (decClock returned.2) else 0
  have following : ∀ (result : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (body, s) = (result, middle) →
      contLoop result = true → middle.clock ≠ 0 →
      BoundedFlattenProp (.loop body) (decClock middle) rest := by
    intro result middle run continuing positive
    have restEq : rest = stackWork (.loop body) (decClock middle) := by
      simp [rest, returned, run, continuing, positive]
    rw [restEq]
    exact next result middle run continuing positive
  have composed := flattenLoop_reached_bounded s body (stackWork body s) rest first following
  intro t r final n l cs bs target hyps
  apply boundedFlattenConcl_mono (a := stackWork body s + rest) _
    (composed t r final n l cs bs target hyps)
  rw [stackWork, StackSemEvaluateClock.fixClockEvaluate]
  change stackWork body s + rest ≤ 2 + stackWork body s + rest
  omega

/-- The conservative branch budget discharges both emitted conditional paths. -/
theorem stackWork_if_bound {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp a s (stackWork a s))
    (second : BoundedFlattenProp b s (stackWork b s)) :
    BoundedFlattenProp (.ite cmp r ri a b) s (stackWork (.ite cmp r ri a b) s) := by
  have first' : BoundedFlattenProp a s (stackWork a s + stackWork b s) := by
    intro t result final n l cs bs target hyps
    exact boundedFlattenConcl_mono (Nat.le_add_right _ _) (first t result final n l cs bs target hyps)
  have second' : BoundedFlattenProp b s (stackWork a s + stackWork b s) := by
    intro t result final n l cs bs target hyps
    exact boundedFlattenConcl_mono (Nat.le_add_left _ _) (second t result final n l cs bs target hyps)
  have combined := flattenIf_bounded s cmp r ri a b (stackWork a s + stackWork b s) first' second'
  rw [stackWork]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

#print axioms stackWork_if_bound

#print axioms stackWork_seq_bound
#print axioms stackWork_loop_bound

#print axioms stackWork
end InitECandidate.Runtime.StackToLab
