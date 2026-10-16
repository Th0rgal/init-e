import InitECandidate.Runtime.GasFunding

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact source body of the minimum helper used to cap spill refunds. -/
theorem source_min_body : sourceFunctionBody Guest.guestFn_min =
    .seq (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
      (.return (.var .local (ofString "a"))) .skip)
      (.return (.var .local (ofString "b"))) := by cbv

/-- Actual authoritative evaluator execution, at any source clock: the refund
cap helper returns the unsigned word minimum and preserves that clock. -/
theorem evaluate_source_min {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (left right : BitVec 64)
    (hLeft : state.locals.lookup (ofString "a") = some (.val (.word left)))
    (hRight : state.locals.lookup (ofString "b") = some (.val (.word right))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_min) =
      (some (.returned (.val (.word (wordMin left right)))), emptyLocalsHOLFinite state) := by
  classical
  rw [source_min_body]
  by_cases lower : left.toNat < right.toNat
  all_goals simp [evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite,
    evaluateHOLFiniteState_return, evalHOLExact, toExact, hLeft, hRight,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
    shapeOfHOLExact, sizeOfShapeWithContextHOL, wordMin, lower,
    fixClockHOLFinite, emptyLocalsHOLFinite]

/-- Exact spent-counter expression stored first by `frame_halt`. -/
def frameHaltStoredUsed : ExpHOL 64 :=
  match sourceFunctionBody Guest.guestFn_frame_halt with
  | .seq (.store _ value) _ => value
  | _ => .const 0

def fundingLoad (offset : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [.var .global (ofString "ev"), .const offset])

theorem frameHaltStoredUsed_eq : frameHaltStoredUsed =
    .op .add [fundingLoad 184, fundingLoad 64] := by cbv

theorem eval_fundingLoad {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame offset value : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : state.memaddrs (frame + offset))
    (memory : state.memory (frame + offset) = .word value) :
    @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (fundingLoad offset) =
      some (.val (.word value)) := by
  classical
  simp [fundingLoad, evalHOLExact, evalListHOLExact, toExact, hFrame,
    wordOpHOL, wordOp, valueIsWord, valueWord, isWfShapeExactHOL,
    memLoadHOLExact, domain, memory]

theorem eval_frameHaltStoredUsed {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (frame left used : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64))
    (usedDomain : state.memaddrs (frame + 184))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used) :
    @evalHOLExact 64 σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) frameHaltStoredUsed =
      some (.val (.word (used + left))) := by
  classical
  rw [frameHaltStoredUsed_eq]
  simp only [evalHOLExact, evalListHOLExact]
  rw [eval_fundingLoad state frame 184 used hFrame usedDomain usedMemory,
    eval_fundingLoad state frame 64 left hFrame leftDomain leftMemory]
  simp [valueIsWord, valueWord, wordOpHOL, wordOp]

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.evaluate_source_min
#print axioms InitECandidate.Runtime.eval_frameHaltStoredUsed
