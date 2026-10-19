import InitECandidate.Runtime.WitnessDecodeModeMeasure
import InitECandidate.Runtime.WitnessTraversalStateMeasure
import InitECandidate.Runtime.WitnessModeCallerLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_decode_mode_state_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array previous : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
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
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (input inputLength : BitVec 64) (persistentFloor : Nat)
    (floorAbove : ceiling ≤ persistentFloor) (floorBeforeHeap : persistentFloor ≤ array.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (stack : WitnessAllocationStack s input inputLength array persistentFloor ceiling previous)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (oldMode : s.locals.lookup (ofString "mode")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode = (none,post)) : witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  have rank := witness_decode_mode_measure_decreases s post table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap
    input inputLength persistentFloor floorAbove floorBeforeHeap spanLo spanHi stack run
  have postRunning := (witness_decode_go_normal_kept s post run).trans running
  have before := witnessTraversalStateMeasure_running s frame previous running atTop
  rw [witnessTraversalModeCredit_decode s oldMode] at before
  rcases rank with ⟨mode,top,decreases⟩ | ⟨record,mode,top,decreases⟩
  · have after := witnessTraversalStateMeasure_running post frame previous postRunning top
    rw [witnessTraversalModeCredit_delivery post mode] at after
    rw [before,after]
    exact decreases
  · have after := witnessTraversalStateMeasure_running post frame record postRunning top
    rw [witnessTraversalModeCredit_resolve post mode] at after
    rw [before,after]
    exact decreases

#print axioms witness_decode_mode_state_measure_decreases
end InitECandidate.Runtime
