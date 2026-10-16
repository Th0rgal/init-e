import InitECandidate.Runtime.BaselineInitializerFields
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyPanToWord
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend.StackRemove

theorem baseline_heap_low :
    (BitVec.ofNat 64 sourceBase) + BitVec.ofNat 64 maxStackAlloc * bytesInWord 64 ≤ BitVec.ofNat 64 stackStart := by decide_cbv

theorem baseline_heap_high :
    BitVec.ofNat 64 stackStart ≤ (BitVec.ofNat 64 ramEnd) - BitVec.ofNat 64 maxStackAlloc * bytesInWord 64 := by decide_cbv

theorem baseline_heap_fits :
    (-1 * (BitVec.ofNat 64 sourceBase) + BitVec.ofNat 64 stackStart).toNat ≤ entryHeapLimit * (bytesInWord 64).toNat := by decide_cbv

theorem baseline_heap_limit_fits : (bytesInWord 64).toNat * entryHeapLimit < 2 ^ 64 := by decide_cbv

theorem baseline_heap_aligned :
    holAligned (wordShiftAmount 64 + 1)
      ((BitVec.ofNat 64 stackStart) + -1 * BitVec.ofNat 64 sourceBase) = true := by decide_cbv

#print axioms baseline_heap_low
#print axioms baseline_heap_high
#print axioms baseline_heap_fits
#print axioms baseline_heap_limit_fits
#print axioms baseline_heap_aligned
end InitECandidate.Runtime
