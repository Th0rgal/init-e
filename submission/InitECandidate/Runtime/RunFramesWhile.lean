import InitECandidate.Runtime.RunFramesIteration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def runFramesWhile : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) runFramesLoopBody

/-- The actual while semantics charges one clock before entering the body.
A successful body that does not increase the remaining clock resumes the loop. -/
theorem evaluate_runFrames_while_step {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (go : BitVec 64)
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (running : go ≠ 0) (clock : state.clock ≠ 0)
    (body : evaluateHOLFiniteState (decClockHOLFinite state) runFramesLoopBody = (none,post))
    (clockBound : post.clock ≤ (decClockHOLFinite state).clock) :
    evaluateHOLFiniteState state runFramesWhile = evaluateHOLFiniteState post runFramesWhile := by
  classical
  unfold runFramesWhile
  rw [evaluateHOLFiniteState_while_total]
  have runningLiteral : go ≠ (0#64) := running
  simp only [evalHOLFinite,evalHOLExact,goLocal]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  simp [runningLiteral,clock,body,fixClockHOLFinite,Nat.not_lt.mpr clockBound]

/-- Clearing go exits without spending another source clock. -/
theorem evaluate_runFrames_while_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word 0))) :
    evaluateHOLFiniteState state runFramesWhile = (none,state) := by
  classical
  unfold runFramesWhile
  rw [evaluateHOLFiniteState_while_total]
  simp [evalHOLFinite,evalHOLExact,goLocal,Compiler.Encoders.Asm.wordCmpHOL]

/-- A finite chain of real loop-body executions, ending with a cleared go
flag. This records execution evidence rather than replacing the evaluator. -/
inductive RunFramesTrace {F : Type} :
    PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop where
  | done (state : PanSemStateFiniteExact 64 F)
      (go : state.locals.lookup (ofString "go") = some (.val (.word 0))) :
      RunFramesTrace state state 0
  | step (state next post : PanSemStateFiniteExact 64 F) (go : BitVec 64) (count : Nat)
      (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
      (running : go ≠ 0) (clock : state.clock ≠ 0)
      (body : evaluateHOLFiniteState (decClockHOLFinite state) runFramesLoopBody = (none,next))
      (clockBound : next.clock ≤ (decClockHOLFinite state).clock)
      (tail : RunFramesTrace next post count) : RunFramesTrace state post (count + 1)

/-- Any such finite chain is a successful execution of the authoritative while. -/
theorem RunFramesTrace.evaluate {F : Type} {state post : PanSemStateFiniteExact 64 F} {count : Nat}
    (trace : RunFramesTrace state post count) :
    evaluateHOLFiniteState state runFramesWhile = (none,post) := by
  induction trace with
  | done state go => exact evaluate_runFrames_while_done state go
  | step state next post go count goLocal running clock body clockBound tail ih =>
      rw [evaluate_runFrames_while_step state next go goLocal running clock body clockBound]
      exact ih

/-- Every real iteration consumes at least its guard clock, so the number of
iterations in a successful chain is bounded by its available source clock. -/
theorem RunFramesTrace.clock_bound {F : Type} {state post : PanSemStateFiniteExact 64 F} {count : Nat}
    (trace : RunFramesTrace state post count) : post.clock + count ≤ state.clock := by
  induction trace with
  | done state go => omega
  | step state next post go count goLocal running clock body clockBound tail ih =>
      change next.clock ≤ state.clock - 1 at clockBound
      omega

#print axioms RunFramesTrace.evaluate
#print axioms RunFramesTrace.clock_bound
#print axioms evaluate_runFrames_while_step
#print axioms evaluate_runFrames_while_done
end InitECandidate.Runtime
