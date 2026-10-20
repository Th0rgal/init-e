import InitECandidate.Runtime.ScratchAllocationAligned
import InitECandidate.Runtime.WitnessTraversalStateTransport
import InitECandidate.Runtime.WitnessDecodeAllocationStack
import InitECandidate.Runtime.WitnessDecodeResultAboveStack
import InitECandidate.Runtime.WitnessDecodeModeDatabaseFrame
import InitECandidate.Runtime.WitnessDecodeScratchChain
import InitECandidate.Runtime.WitnessDecodeModeSelectedSlot
import InitECandidate.Runtime.WitnessDecodeCompletedNodeEnvelope
import InitECandidate.Runtime.WitnessModeCallerLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Actual normally completed decode mode preserves every component of the
concrete traversal invariant. No additional caller condition is assumed. -/
theorem WitnessTraversalState.decode_memory_frame {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (decode : mode=1)
    (budget : decodeStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) : ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.persistentFloor→post.memory watched=s.memory watched := by
  obtain ⟨pointer,length,atPointer,atLength,spanLo,spanHi,inputRange,size⟩ := valid.decodeInput decode
  have lengthBound := size.trans valid.inputBound
  have limit:=valid.inputLimitBound
  have scratchLo:=valid.scratchLower
  have scratchHi:=valid.scratchBound
  have db:=valid.scratchBeforeDatabase
  have floor:=valid.databaseBeforeFloor
  have heapLo:=valid.floorBeforeHeap
  have before:=valid.inputBeforeFloor
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have countLimit : layout.inputLimit*16<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have heapArena : ∀ a : BitVec 64, heap.toNat≤a.toNat → a.toNat<33806089496 → s.memaddrs a := by
    intro a lo hi;exact valid.heapArena a (by omega) hi
  have beforeFrame : pointer.toNat+length.toNat≤layout.frame.toNat ∨ (scratch.toNat%8=0 ∧ scratch.toNat≤pointer.toNat) := by
    rcases valid.inputBeforeFrame with below | above
    · exact Or.inl (by omega)
    · exact Or.inr ⟨valid.scratchAligned,by omega⟩
  have beforeHeap : pointer.toNat+length.toNat≤heap.toNat := by omega
  have arrayAbove : scratch.toNat≤heap.toNat := by omega
  have floorAbove : scratch.toNat≤layout.persistentFloor := by omega
  obtain ⟨nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_decode_mode_normal_heap_frame s post
    layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit run
  intro watched lo hi
  exact memory watched (by omega) (by omega)
#print axioms WitnessTraversalState.decode_memory_frame
end InitECandidate.Runtime
