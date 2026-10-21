import InitECandidate.Runtime.WordStackValueTailCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 4000000

/-- A newly pushed frame has the same keys on both runs. If the callee
preserves those keys and transports frame values, its returned head frames
are equal; only the older saved stack below them may differ. -/
theorem same_pushed_frame_head (head : WordSemStackFrame 64)
    (sourceOuter targetOuter sourceStack targetStack : List (WordSemStackFrame 64))
    (sourceKeys : sKeyEq (head :: sourceOuter) sourceStack)
    (targetKeys : sKeyEq (head :: targetOuter) targetStack)
    (values : sValEq sourceStack targetStack) :
    ∃ frame sourceTail targetTail,
      sourceStack = frame :: sourceTail ∧ targetStack = frame :: targetTail ∧ sValEq sourceTail targetTail := by
  cases sourceStack with
  | nil => simp [sKeyEq] at sourceKeys
  | cons sourceHead sourceTail =>
    cases targetStack with
    | nil => simp [sKeyEq] at targetKeys
    | cons targetHead targetTail =>
      have keys := sFrameKeyEqTrans sourceHead head targetHead
        ⟨(sFrameKeyEqSym head sourceHead).mp sourceKeys.2, targetKeys.2⟩
      have heads := sValAndKeyEq [sourceHead] [targetHead]
        ⟨⟨True.intro, values.2⟩, ⟨True.intro, keys⟩⟩
      have equal : sourceHead = targetHead := (List.cons.inj heads).1
      subst targetHead
      exact ⟨sourceHead, sourceTail, targetTail, rfl, rfl, values.1⟩

/-- Pop the real equal returned frame. The restored caller locals, handler,
clock and all other fields agree, with value-equal older stacks remaining. -/
theorem pop_same_frame_stack_value {C F : Type}
    (source popped : WordSemStateFiniteExact 64 C F) (head : WordSemStackFrame 64)
    (sourceTail targetTail : List (WordSemStackFrame 64))
    (shape : source.stack = head :: sourceTail) (values : sValEq sourceTail targetTail)
    (actual : popEnv source = some popped) :
    popEnv {source with stack := head :: targetTail} = some {popped with stack := targetTail} ∧
      sValEq popped.stack targetTail := by
  rcases head with ⟨size, first, roots, handler⟩
  cases handler
  all_goals simp only [popEnv, shape, Option.some.injEq] at actual
  all_goals subst popped
  all_goals exact ⟨rfl, values⟩

/-- Construct the actual entry to the same callee after a returning call.
The original semantic stack-size relation discharges every metadata field. -/
theorem pushed_callee_stack_value {C F : Type}
    (source : WordSemStateFiniteExact 64 C F) (stack : List (WordSemStackFrame 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (arguments : List (WordLocW 64)) (size : Option Nat)
    (values : sValEq source.stack stack) :
    ∃ frame,
      (WordSemStateFiniteExact.callEnv arguments size (pushEnv envs handler source)).stack = frame :: source.stack ∧
      WordSemStateFiniteExact.callEnv arguments size (pushEnv envs handler {source with stack := stack}) =
        {WordSemStateFiniteExact.callEnv arguments size (pushEnv envs handler source) with stack := frame :: stack} ∧
      sValEq (WordSemStateFiniteExact.callEnv arguments size (pushEnv envs handler source)).stack (frame :: stack) := by
  obtain ⟨frame, shape, pushed⟩ := pushEnv_withStack envs handler source stack values
  have extended : sValEq (pushEnv envs handler source).stack (frame :: stack) := by
    rw [shape]
    exact ⟨values, of_eq_true (sFrameValEqRefl frame)⟩
  refine ⟨frame, shape, ?_, extended⟩
  rw [pushed]
  exact callEnv_withStack arguments size (pushEnv envs handler source) (frame :: stack) extended

/-- An exception caught by the newly pushed top frame restores identical
caller locals on both runs. Only the older saved stack is substituted. -/
theorem stack_value_top_exception {C F : Type} (body : WordLangProgHOL (BitVec 64))
    (source post : WordSemStateFiniteExact 64 C F) (location payload : WordLocW 64)
    (frame : WordSemStackFrame 64) (sourceOuter targetOuter : List (WordSemStackFrame 64))
    (shape : source.stack = frame :: sourceOuter)
    (top : source.handler + 1 = source.stack.length)
    (related : sValEq source.stack (frame :: targetOuter))
    (actual : evaluate body source = (some (.exception location payload), post)) :
    ∃ afterStack,
      evaluate body {source with stack := frame :: targetOuter} =
        (some (.exception location payload), {post with stack := afterStack}) ∧
      sValEq post.stack afterStack := by
  have transport := evaluateStackSwap body source
  unfold stackSwapPost at transport
  rw [actual] at transport
  obtain ⟨bounded, first, roots, handler, tail, size, returned,
    handlerFrame, sameSize, locals, keys, handlerEq, swapped⟩ := transport
  rw [lastNLengthCond _ _ top, shape] at handlerFrame
  obtain ⟨frameEq, outerEq⟩ := List.cons.inj handlerFrame
  subst frame
  subst tail
  have targetTop : source.handler + 1 =
      (WordSemStackFrame.stackFrame size first roots (some handler) :: targetOuter).length :=
    top.trans (sValEqLength _ _ related)
  have targetFrame : wordSemLastN (source.handler + 1)
      (WordSemStackFrame.stackFrame size first roots (some handler) :: targetOuter) =
      WordSemStackFrame.stackFrame size first roots (some handler) :: targetOuter :=
    lastNLengthCond _ _ targetTop
  obtain ⟨afterStack, afterLocals, run, ⟨newReturned, newKeys, newLocals, newValues⟩, afterValues, afterKeys⟩ :=
    swapped _ first roots targetOuter ⟨targetFrame, related⟩
  have returnedEq : returned = newReturned :=
    listEq_of_map_fst_snd returned newReturned (locals.1.symm.trans newKeys) newValues
  have localsEq : afterLocals = post.locals := by
    rw [newLocals, ← returnedEq, ← locals.2]
  refine ⟨afterStack, ?_, afterValues⟩
  simpa only [localsEq, ← handlerEq] using run

#print axioms stack_value_top_exception
#print axioms same_pushed_frame_head
#print axioms pop_same_frame_stack_value
#print axioms pushed_callee_stack_value
end InitECandidate.Runtime.FineCost
