import InitECandidate.Runtime.RlpHeaderLongStringReadBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual length-reader declaration carries payload progress into its
caller, including the case where validation runs with no source ticks left. -/
theorem rlpHeader_long_string_read_return_reader {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer headerLength total : BitVec 64) (finalValue : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 2 ≤ state.clock)
    (evaluated : evaluateHOLFiniteState state rlpHeaderLongStringRead = (some (.returned finalValue),final)) :
    ∃ (payload : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) headerLength))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word payload))),readerPost) ∧
      finalValue = rlpHeaderLongStringValue headerLength payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + (headerLength + payload)).toNat ∧ (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  let arguments : List (ExpHOL 64) := [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee := rlpReadLengthCallee (pointer + 1) headerLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "n") = some (.val (.word headerLength)) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ := evaluate_rlpReadLength_body_bounded entry
    (pointer + 1) headerLength atPointer atLength code (by change headerLength.toNat + 1 ≤ state.clock - 1; omega)
  have entryClock : entry.clock = state.clock - 1 := rfl
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) (pointer + 1) headerLength (by decide) installed
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_read_length)
  rw [run] at metadata
  dsimp only at metadata
  have callRun := evaluated
  rw [source_rlpHeader_long_string_read] at callRun
  obtain ⟨value,actual,ready,output,actualRun,locals,_,_,_,readyCode,tail,_⟩ :=
    evaluate_decCall_returned_body_scope state final (ofString "n") (ofString "rlp_read_length") .one .one
      arguments [.val (.word (pointer + 1)),.val (.word headerLength)]
      (sourceFunctionBody Guest.guestFn_rlp_read_length) rlpHeaderLongStringFinish callee finalValue args lookup callRun
  have same := Prod.mk.inj (run.symm.trans actualRun)
  have actualEq : post = actual := same.2
  subst actual
  obtain ⟨payload,rfl⟩ := returned value same.1
  let resumed := setVarHOLFinite (ofString "n") (.val (.word payload)) ready
  have atLL : resumed.locals.lookup (ofString "ll") = some (.val (.word headerLength)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "ll" by decide] using headerLocal
  have atTotal : resumed.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have atPayload : resumed.locals.lookup (ofString "n") = some (.val (.word payload)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atPointerResumed : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "p" by decide] using pointerLocal
  have shape := rlpHeader_long_string_finish_value resumed output headerLength payload finalValue
    atLL atPayload (readyCode.trans (metadata.1.trans code)) tail
  exact ⟨payload,post,actualRun,shape,rlpHeader_long_string_finish_progress resumed output pointer headerLength payload total finalValue
    atPointerResumed atLL atPayload atTotal headerFits (readyCode.trans (metadata.1.trans code)) tail⟩

#print axioms rlpHeader_long_string_read_return_reader
end InitECandidate.Runtime
