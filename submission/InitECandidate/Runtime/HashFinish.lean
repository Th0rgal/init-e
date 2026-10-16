import InitECandidate.Runtime.HashFast32Syntax
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashMixFirst (hash : BitVec 64) : BitVec 64 := hash ^^^ (hash >>> 32)
def hashMixSecond (hash : BitVec 64) : BitVec 64 := hashMixFirst hash * 1099511628211
def hashFinishValue (hash : BitVec 64) : BitVec 64 := hashMixSecond hash ^^^ (hashMixSecond hash >>> 29)

/-- Actual final xor/shift/multiply sequence returns the mixed hash without
spending source clocks or changing memory or any nonlocal state field. -/
theorem evaluate_hashFinish {F : Type} (state : PanSemStateFiniteExact 64 F) (hash : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash))) :
    evaluateHOLFiniteState state hashFinish =
      (some (.returned (.val (.word (hashFinishValue hash)))),
        emptyLocalsHOLFinite (setVarHOLFinite (ofString "h") (.val (.word (hashMixSecond hash)))
          (setVarHOLFinite (ofString "h") (.val (.word (hashMixFirst hash))) state))) := by
  have firstValue : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .xor [.var .local (ofString "h"),.shift .lsr (.var .local (ofString "h")) (.const 32)]) =
        some (.val (.word (hashMixFirst hash))) := by
    simp [evalHOLExact,evalListHOLExact,hashLocal,wordShiftHOL,wordOpHOL,wordOp,valueIsWord,valueWord,hashMixFirst]
  have first := evaluate_local_word_assignment state (ofString "h") _ hash _ hashLocal firstValue
  let middle := setVarHOLFinite (ofString "h") (.val (.word (hashMixFirst hash))) state
  have h : middle.locals.lookup (ofString "h") = some (.val (.word (hashMixFirst hash))) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have secondValue : @evalHOLExact 64 F _ middle.toExact
      (fun address => Classical.propDecidable (middle.memaddrs address))
      (.panop .mul [.var .local (ofString "h"),.const 1099511628211]) =
        some (.val (.word (hashMixSecond hash))) := by
    simp [evalHOLExact,evalListHOLExact,h,panOpHOL,valueIsWord,valueWord,hashMixSecond]
  have second := evaluate_local_word_assignment middle (ofString "h") _ _ _ h secondValue
  let finalState := setVarHOLFinite (ofString "h") (.val (.word (hashMixSecond hash))) middle
  have finalLocal : finalState.locals.lookup (ofString "h") = some (.val (.word (hashMixSecond hash))) := by
    simp [finalState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have returned : evaluateHOLFiniteState finalState
      (.return (.op .xor [.var .local (ofString "h"),.shift .lsr (.var .local (ofString "h")) (.const 29)])) =
      (some (.returned (.val (.word (hashFinishValue hash)))),emptyLocalsHOLFinite finalState) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,finalLocal,wordShiftHOL,
      wordOpHOL,wordOp,valueIsWord,valueWord,hashFinishValue,shapeOfHOLExact]
  unfold hashFinish
  rw [evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,second]
  exact returned

/-- Sequence association composes a checked word step with its source
continuation, retaining the exact two-local state update. -/
theorem evaluate_hashWordThen {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord value : BitVec 64) (offset : Nat) (continuation : ProgHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (domain : state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (cell : state.memory (pointer + BitVec.ofNat 64 offset) = .word value) :
    evaluateHOLFiniteState state (hashWordThen offset continuation) =
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
        (setVarHOLFinite (ofString "w") (.val (.word value)) state)) continuation := by
  have step := evaluate_hashWordStep state pointer hash oldWord value offset pointerLocal hashLocal wordLocal domain cell
  change evaluateHOLFiniteState state (.seq _ (.seq _ continuation)) = _
  rw [← evaluate_seq_assoc]
  change evaluateHOLFiniteState state (.seq (hashWordStep offset) continuation) = _
  rw [evaluateHOLFiniteState_seq_line780,step]

#print axioms evaluate_hashFinish
#print axioms evaluate_hashWordThen
end InitECandidate.Runtime
