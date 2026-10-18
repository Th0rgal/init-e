import InitECandidate.Runtime.VersionedHashesGuardedInitialization
import InitECandidate.Runtime.VersionedHashesGuardedLoopReturnBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_guarded_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame heap : BitVec 64) (ceiling : Nat)
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (small : count.toNat < 2^63) (code : state.code = originalRuntimeCode)
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (aligned : heap.toNat % 8 = 0) (heapBound : heap.toNat ≤ 33806089496)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (heapAbove : ceiling ≤ heap.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (arrayAbove : ceiling ≤ array.toNat)
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (budget : count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (versionedHashesAt 5)
    state.clock ≤ evaluated.2.clock + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "k") (.val (.word 0)) state
  let ready := versionedHashesInitialState state
  let valid := versioned_hashes_initial_guarded_runtime_invariant state count array vh input inputLength scratch frame heap ceiling
    countLocal arrayLocal vhLocal small code slices heapGlobal scratchGlobal frameGlobal aligned heapBound arena heapArena
    inputBeforeHeap arrayBeforeHeap heapAbove
  have rank : versionedHashesRank count ready = count.toNat := by
    simp [ready,versionedHashesRank,versionedHashesInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_versioned_hashes_guarded_loop_return_bounded ready count array vh input inputLength scratch frame ceiling inputLimit
    valid inputBound limitBound orderedFrame framePositive scratchBelow inputBeforeFrame arrayAbove countLimit (by rw [rank]; exact budget)
  rw [rank] at bounded
  have initial (current : PanSemStateFiniteExact 64 F) : @evalHOLExact 64 F _ current.toExact
      (fun address => Classical.propDecidable (current.memaddrs address)) (.const 0) = some (.val (.word (0 : BitVec 64))) := rfl
  have checked : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [source_versioned_hashes_initialization,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial state]
  dsimp only
  rw [checked,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial entered]
  dsimp only
  rw [checked]
  exact bounded

#print axioms evaluate_versioned_hashes_guarded_initialized_bounded
end InitECandidate.Runtime
