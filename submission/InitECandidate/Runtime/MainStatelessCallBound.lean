import InitECandidate.Runtime.MainSszHandlerBound
import InitECandidate.Runtime.StatelessInputHandledCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mainStatelessCall : ProgHOL 64 :=
  .call (some (some (.local,ofString "si"),some (ofString "SszErr",ofString "err_code",mainSszHandler)))
    (ofString "decode_stateless_input") mainStatelessArguments

theorem source_main_stateless_call_head : mainAt 20 = .seq mainStatelessCall (mainAt 21) :=
  source_main_stateless_call

/-- Main's actual handled decoder call costs at most the complete decoder
call bound plus 65 ticks for serialization/output/halt on rejection. -/
theorem evaluate_main_stateless_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer output zeroRoot : BitVec 64)
    (atInput : state.locals.lookup (ofString "inp") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atZeroRoot : state.locals.lookup (ofString "z32") = some (.val (.word zeroRoot)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : statelessInputBound length + 66 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state mainStatelessCall
    state.clock ≤ evaluated.2.clock + (statelessInputBound length + 66) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      mainStatelessArguments = some [.val (.word pointer),.val (.word length)] := by
    simp [mainStatelessArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atInput]
  change state.clock ≤ (evaluateHOLFiniteState state mainStatelessCall).2.clock +
      (statelessInputBound length + 1 + 65) ∧ _
  apply evaluate_stateless_input_handled_call_bounded state (some (.local,ofString "si")) mainStatelessArguments
    (ofString "SszErr") (ofString "err_code") mainSszHandler 65 pointer length offsets heapPointer
    arguments atOffsets code heap heapBound aligned scratchBelow inputFits heapArena domain0 domain8 domain16 domain24
    (by omega)
  intro value post run enough
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state (statelessInputCallee pointer length))
    (sourceFunctionBody Guest.guestFn_decode_stateless_input)
  rw [run] at metadata
  let resumed := setVarHOLFinite (ofString "err_code") value {post with locals := state.locals}
  apply evaluate_mainSszHandler_bounded resumed output zeroRoot ?_ ?_ (metadata.1.trans code) enough
  · simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atOutput,
      show ofString "err_code" ≠ ofString "out" by decide]
  · simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atZeroRoot,
      show ofString "err_code" ≠ ofString "z32" by decide]

#print axioms evaluate_main_stateless_call_bounded
end InitECandidate.Runtime
