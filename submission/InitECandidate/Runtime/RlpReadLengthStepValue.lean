import InitECandidate.Runtime.RlpReadLengthStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful byte read determines the original decoder's accumulator
update exactly, independently of globals, code and unrelated locals. -/
theorem evaluate_rlpReadLength_step_loaded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer index value : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (byte : UInt8)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) = some byte) :
    evaluateHOLFiniteState state rlpReadLengthStep =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
        (setVarHOLFinite (ofString "v") (.val (.word ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte.toNat))) state)) := by
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
  rw [source_rlpReadLength_step,evaluateHOLFiniteState_seq_line780,first]
  exact second


/-- Normal completion exposes the actual input byte and exact updated value. -/
theorem rlpReadLength_step_normal_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer index value : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (run : evaluateHOLFiniteState state rlpReadLengthStep = (none,post)) :
    ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) = some byte ∧
      post.locals.lookup (ofString "v") = some (.val (.word ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte.toNat))) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) with
  | none =>
    rw [source_rlpReadLength_step,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign] at run
    simp [evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,valueLocal,wordShiftHOL,
      wordOpHOL,wordOp,valueIsWord,valueWord,loaded] at run
  | some byte =>
    have actual := evaluate_rlpReadLength_step_loaded state pointer index value pointerLocal indexLocal valueLocal byte loaded
    have same := (Prod.mk.inj (run.symm.trans actual)).2
    rw [same]
    refine ⟨byte,rfl,?_,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "v" by decide]
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rlpReadLength_step_normal_value

#print axioms evaluate_rlpReadLength_step_loaded
end InitECandidate.Runtime
