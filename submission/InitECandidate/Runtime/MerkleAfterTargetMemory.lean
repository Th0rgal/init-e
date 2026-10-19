import InitECandidate.Runtime.MerkleMarkMemory
import InitECandidate.Runtime.MerkleEmptyMemory
import InitECandidate.Runtime.PanSequenceStopped
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

theorem merkleAfterTarget_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengths : MerkleChunkLengths n ((1#64) <<< initial.toNat))
    (depthBound : initial.toNat ≤ 27)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 16 + (1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16))))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have emptyBudget : 16 ≤ state.clock := (Nat.le_add_right 16 _).trans budget
  have positiveBudget : 1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)))) ≤ state.clock := (Nat.le_add_left _ 16).trans budget
  rw [source_merkleEmpty_sequence] at run
  by_cases zero : n = (0#64)
  · have checked : evaluateHOLFiniteState state merkleEmptyCheck = evaluateHOLFiniteState state merkleEmptyBranch := by
      rw [source_merkleEmpty_check,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,atN,zero,Compiler.Encoders.Asm.wordCmpHOL]
    have stopped : (evaluateHOLFiniteState state merkleEmptyCheck).1 ≠ none := by
      rw [checked]
      exact merkleEmpty_branch_terminal state
    rw [evaluate_sequence_stopped state merkleEmptyCheck (merkleizeAt 4) stopped,checked] at run
    exact merkleEmpty_branch_returned_memory state post zeroHashes target out watched value
      atZero atTarget atOut outAligned outFits outOutside code emptyBudget run
  · have checked : evaluateHOLFiniteState state merkleEmptyCheck = (none,state) := by
      rw [source_merkleEmpty_check,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,atN,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,checked] at run
    exact merkleMark_suffix_returned_memory state post pointer accelerator buf zeroHashes initial target out n input watched value
      atPointer atAccel atZero heap heapBound atIndex atTarget atN atInput lengths depthBound atOut
      outAligned outFits outOutside small limit aligned before accelAligned accelFits pointerFits
      accelOutside pointerOutside code positiveBudget run

#print axioms merkleAfterTarget_returned_memory
end InitECandidate.Runtime
