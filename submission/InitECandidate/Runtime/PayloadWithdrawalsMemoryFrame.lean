import InitECandidate.Runtime.PayloadWithdrawalsSuffixBound
import InitECandidate.Runtime.PayloadStoreTailMemoryFrame
import InitECandidate.Runtime.SszFixedListCountDeclarationReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned withdrawal suffix preserves every watched word separated
from its final header stores, and preserves all allocator globals. -/
theorem payload_withdrawals_returned_memory_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (payload withdrawals balance watched : BitVec 64)
    (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (separate : ∀ offset : BitVec 64, offset ∈ ([48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
      watched ≠ payload + offset)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 19) = (some (.returned value),post)) :
    post.memory watched = state.memory watched ∧ post.globals = state.globals := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadWithdrawalsCountArguments =
      some [.val (.word (balance - withdrawals)),.val (.word (44 : BitVec 64)),.val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadWithdrawalsCountArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atWithdrawals,atBalance,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_withdrawals_count] at run
  obtain ⟨_,_,bodyPost,output,memory,globals,domain,tail,postMemory,postGlobals,_⟩ :=
    sszFixedListCount_declaration_returned_frame state (ofString "nwd") (payloadAt 20)
      payloadWithdrawalsCountArguments (balance - withdrawals) 44 9223372036854775807 args code (by decide) post value run
  let entry := setVarHOLFinite (ofString "nwd") (.val (.word ((balance - withdrawals) / 44)))
    {bodyPost with locals := state.locals}
  have atPl : entry.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPayload,
      show ofString "nwd" ≠ ofString "pl" by decide]
  have atNwd : entry.locals.lookup (ofString "nwd") = some (.val (.word ((balance - withdrawals) / 44))) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame := evaluate_payload_store_tail_memory_frame entry payload ((balance - withdrawals) / 44)
    watched atPl atNwd separate
  have globalFrame := evaluate_payload_store_tail_bounded entry
  change evaluateHOLFiniteState entry (payloadAt 20) = _ at tail
  rw [tail] at frame globalFrame
  have outputGlobals : output.globals = entry.globals := by
    apply HolFiniteMapExact.ext
    funext key
    exact globalFrame.2.2 key
  exact ⟨(congrFun postMemory _).trans (frame.trans (congrFun memory _)),
    postGlobals.trans (outputGlobals.trans globals)⟩

#print axioms payload_withdrawals_returned_memory_frame
end InitECandidate.Runtime
