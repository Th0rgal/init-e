import InitECandidate.Runtime.DecodeStepUniformBodyBound
import InitECandidate.Runtime.WitnessDecodeModeSource
import InitECandidate.Runtime.OriginalDecodeStepCode
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_witness_decode_mode {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atPointer : s.locals.lookup (ofString "cur_p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "cur_n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit + 1 ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) :
    RunBounded s decodeWitnessNodeDecodeMode (decodeStepBodyCost inputLimit + 1) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "db",.val (.word table))).update
    (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "cur_p"),.var .local (ofString "cur_n")] =
      some [.val (.word table),.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atPointer,atLength]
  have lookup := pan_three_word_shape_lookup s.code.lookup (ofString "_decode_step")
    (ofString "db") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn__decode_step)
    (.comb [.one,.one]) table pointer length (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeStep_lookup)
  have bounded := runBounded_decode_step_body entry pointer length scratch frame array ceiling inputLimit
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change decodeStepBodyCost inputLimit ≤ s.clock-1; omega)
    heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap
  have reached : Reaches s decodeWitnessNodeDecodeMode (fun ready => ready.code = originalRuntimeCode)
      (decodeStepBodyCost inputLimit + 1) witnessDecodeTail := by
    rw [source_witness_decode_call]
    apply bounded_decCall_reaches s (ofString "d") (ofString "_decode_step") (.comb [.one,.one]) (.comb [.one,.one])
      _ _ _ _ callee (decodeStepBodyCost inputLimit) _ args lookup (by omega) bounded
    intro value post run shapes
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_step)
    rw [run] at metadata
    exact metadata.1.trans code
  have tail : ProgBounded witnessDecodeTail 0 := by
    apply ProgBounded.straight
    rw [source_witness_decode_tail,source_witness_decode_completed,source_witness_decode_push]
    rfl
  have closed := RunBounded.ofReaches (tailCost := 0) (by simpa using budget) reached
    (fun ready installed ticks => RunBounded.ofProg tail installed ticks)
  simpa using closed

#print axioms runBounded_witness_decode_mode
end InitECandidate.Runtime
