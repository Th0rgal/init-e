import InitECandidate.Runtime.RlpListCountStepConsumed
import InitECandidate.Runtime.RlpItemTotalReturnedHeaderExact
import InitECandidate.Runtime.RlpHeaderBoundaryCases
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful checked count iteration necessarily reads its current header. -/
theorem rlpListCount_normal_step_readable {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offset count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (inside : offset.toNat < length.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post)) :
    ∃ byte : UInt8, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + offset) = some byte := by
  obtain ⟨consumed,bodyPost,bodyRun,_,_,_,_⟩ := rlpListCount_step_consumed state post pointer length offset count
    pointerLocal lengthLocal offsetLocal countLocal code ticks run
  let entry := callEntryStateHOLFinite state (rlpHeaderCallee (pointer + offset) (length - offset))
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + offset))) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word (length - offset))) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨header,payload,kind,headerPost,headerRun,_⟩ := rlpItemTotal_body_returned_header_exact
    entry bodyPost (pointer + offset) (length - offset) (.val (.word consumed)) atPointer atLength code
    (by change 12 ≤ state.clock - 1; omega) bodyRun
  let headerEntry := callEntryStateHOLFinite entry (rlpHeaderCallee (pointer + offset) (length - offset))
  have headerPointer : headerEntry.locals.lookup (ofString "p") = some (.val (.word (pointer + offset))) := by
    simp [headerEntry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have headerLength : headerEntry.locals.lookup (ofString "len") = some (.val (.word (length - offset))) := by
    simp [headerEntry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have nonzero : length - offset ≠ 0 := by
    intro zero
    have natural := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show offset.toNat ≤ length.toNat by omega))
    rw [zero] at natural
    change 0 = length.toNat - offset.toNat at natural
    omega
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + offset) with
  | some byte => exact ⟨byte,rfl⟩
  | none =>
    have stopped := evaluate_rlpHeader_unreadable_header headerEntry (pointer + offset) (length - offset)
      headerPointer headerLength nonzero loaded
    rw [headerRun] at stopped
    cases stopped

#print axioms rlpListCount_normal_step_readable
end InitECandidate.Runtime
