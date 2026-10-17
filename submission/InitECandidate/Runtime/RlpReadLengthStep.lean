import InitECandidate.Runtime.RlpReadLengthSyntax
import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every length-decoder step either stops on a failed byte read or updates
its accumulator and increments the index exactly once, without nested ticks. -/
theorem evaluate_rlpReadLength_step_cases {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer index value : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value))) :
    evaluateHOLFiniteState state rlpReadLengthStep = (some .error,state) ∨
      ∃ next : BitVec 64, evaluateHOLFiniteState state rlpReadLengthStep =
        (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
          (setVarHOLFinite (ofString "v") (.val (.word next)) state)) := by
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) with
  | none =>
    left
    rw [source_rlpReadLength_step,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign]
    simp [evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,valueLocal,wordShiftHOL,
      wordOpHOL,wordOp,valueIsWord,valueWord,loaded]
  | some byte =>
    let next : BitVec 64 := (value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte.toNat
    have expression : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8),
          .loadByte (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])]) = some (.val (.word next)) := by
      simp [evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,valueLocal,wordShiftHOL,
        wordOpHOL,wordOp,valueIsWord,valueWord,loaded,next]
      change (value <<< (8 : Nat)) ||| ((BitVec.ofNat 64 byte.toNat) ||| (0 : BitVec 64)) = _
      simp
    have first := evaluate_local_word_assignment state (ofString "v")
      (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8),
        .loadByte (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])]) value next valueLocal expression
    let middle := setVarHOLFinite (ofString "v") (.val (.word next)) state
    have atIndex : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by
      simpa [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "v" ≠ ofString "i" by decide] using indexLocal
    have second := evaluate_local_word_assignment middle (ofString "i")
      (.op .add [.var .local (ofString "i"),.const 1]) index (index + 1) atIndex
      (by simp [evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord])
    refine Or.inr ⟨next,?_⟩
    rw [source_rlpReadLength_step,evaluateHOLFiniteState_seq_line780,first]
    exact second

#print axioms evaluate_rlpReadLength_step_cases
end InitECandidate.Runtime
