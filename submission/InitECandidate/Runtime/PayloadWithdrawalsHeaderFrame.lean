import InitECandidate.Runtime.PayloadWithdrawalsSuffixBound
import InitECandidate.Runtime.PayloadStoreTailMemoryFrame
import InitECandidate.Runtime.SszFixedListCountDeclarationReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned payload withdrawal suffix preserves the earlier header cells
across both the fixed-list call and every final store. -/
theorem payload_withdrawals_returned_header_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (payload withdrawals balance offset : BitVec 64)
    (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (earlier : offset ∈ ([0,8,16,24,32,40] : List (BitVec 64)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 19) = (some (.returned value),post)) :
    post.memory (payload + offset) = state.memory (payload + offset) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadWithdrawalsCountArguments =
      some [.val (.word (balance - withdrawals)),.val (.word (44 : BitVec 64)),.val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadWithdrawalsCountArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atWithdrawals,atBalance,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_withdrawals_count] at run
  obtain ⟨_,_,bodyPost,output,memory,globals,domain,tail,postMemory,_,_⟩ :=
    sszFixedListCount_declaration_returned_frame state (ofString "nwd") (payloadAt 20)
      payloadWithdrawalsCountArguments (balance - withdrawals) 44 9223372036854775807 args code (by decide) post value run
  let entry := setVarHOLFinite (ofString "nwd") (.val (.word ((balance - withdrawals) / 44)))
    {bodyPost with locals := state.locals}
  have atPl : entry.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPayload,
      show ofString "nwd" ≠ ofString "pl" by decide]
  have atNwd : entry.locals.lookup (ofString "nwd") = some (.val (.word ((balance - withdrawals) / 44))) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame := evaluate_payload_store_tail_header_cells entry payload ((balance - withdrawals) / 44)
    offset atPl atNwd earlier
  change evaluateHOLFiniteState entry (payloadAt 20) = _ at tail
  rw [tail] at frame
  exact (congrFun postMemory _).trans (frame.trans (congrFun memory _))

#print axioms payload_withdrawals_returned_header_frame
end InitECandidate.Runtime
