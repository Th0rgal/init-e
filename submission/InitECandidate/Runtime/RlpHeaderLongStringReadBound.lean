import InitECandidate.Runtime.RlpHeaderLongStringProgress
import InitECandidate.Runtime.RlpReadLengthCallResult
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpHeader_long_string_read : rlpHeaderLongStringRead =
    .decCall (ofString "n") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] rlpHeaderLongStringFinish := by
  simp only [rlpHeaderLongStringRead,rlpHeaderLongStringFinish,rlpHeaderLongStringBody,rlpHeaderLongString,rlpHeaderLongStringBranch,
    rlpHeaderAfterShortString,rlpHeaderAfterSingle,
    rlpHeaderAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual long-string header length declaration plus validation costs at most
ll+3 source ticks, covering all callee and continuation error paths. -/
theorem evaluate_rlpHeader_long_string_read_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpHeaderLongStringRead
    state.clock ≤ evaluated.2.clock + (headerLength.toNat + 3) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  have continuationBound : ∀ value, result = some (.returned value) →
      let resumed := setVarHOLFinite (ofString "n") value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed rlpHeaderLongStringFinish
      resumed.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
    intro value equal
    obtain ⟨word,rfl⟩ := returned value equal
    let resumed := setVarHOLFinite (ofString "n") (.val (.word word)) {post with locals := state.locals}
    have atP : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "n" ≠ ofString "p" by decide] using pointerLocal
    have atLL : resumed.locals.lookup (ofString "ll") = some (.val (.word headerLength)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "n" ≠ ofString "ll" by decide] using headerLocal
    have atN : resumed.locals.lookup (ofString "n") = some (.val (.word word)) := by
      simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨tailResult,tailPost,tailRun,tailCost,tailRemaining,tailNoTimeout,_⟩ := evaluate_rlpHeader_long_string_finish resumed
      headerLength word atLL atN (metadata.1.trans code) (by change 1 ≤ post.clock; omega)
    dsimp only
    change resumed.clock ≤ (evaluateHOLFiniteState resumed rlpHeaderLongStringFinish).2.clock + 1 ∧ _
    rw [tailRun]
    exact ⟨tailCost,tailRemaining,tailNoTimeout⟩
  have bound := evaluate_decCall_continuation_bounded state post (ofString "n") (ofString "rlp_read_length")
    .one .one arguments [.val (.word (pointer + 1)),.val (.word headerLength)]
    (sourceFunctionBody Guest.guestFn_rlp_read_length) rlpHeaderLongStringFinish callee result (headerLength.toNat + 2) 1
    args lookup (by omega) run remaining (by omega) noTimeout continuationBound
  rw [source_rlpHeader_long_string_read]
  exact bound

#print axioms evaluate_rlpHeader_long_string_read_bounded
end InitECandidate.Runtime
