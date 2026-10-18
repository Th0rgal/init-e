import InitECandidate.Runtime.VersionedHashesBodyBound
import InitECandidate.Runtime.OriginalVersionedHashesCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame heap : BitVec 64) (ceiling : Nat)
    (si payload hashCount : BitVec 64)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some [.val (.word si)])
    (payloadDomain : state.memaddrs (si + 0)) (payloadCell : state.memory (si + 0) = .word payload)
    (arrayDomain : state.memaddrs (payload + 32)) (arrayCell : state.memory (payload + 32) = .word array)
    (countDomain : state.memaddrs (payload + 40)) (countCell : state.memory (payload + 40) = .word count)
    (vhDomain : state.memaddrs (si + 8)) (vhCell : state.memory (si + 8) = .word vh)
    (hashCountDomain : state.memaddrs (si + 16)) (hashCountCell : state.memory (si + 16) = .word hashCount)
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
    (frameReserve : heap.toNat + count.toNat * transactionHeapGrowth inputLength.toNat + transactionHeapWorkspace inputLength.toNat ≤ frame.toNat)
    (capReserve : heap.toNat + count.toNat * transactionHeapGrowth inputLength.toNat + transactionHeapWorkspace inputLength.toNat ≤ 33806089496)
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (budget : 1 + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "is_valid_versioned_hashes") arguments)
    state.clock ≤ evaluated.2.clock + (1 + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "si",.val (.word si))
  let entry := callEntryStateHOLFinite state callee
  have atSi : entry.locals.lookup (ofString "si") = some (.val (.word si)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entrySlices : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have bounded := evaluate_versioned_hashes_body_bounded entry count array vh input inputLength scratch frame heap ceiling
    si payload hashCount atSi payloadDomain payloadCell arrayDomain arrayCell countDomain countCell vhDomain vhCell hashCountDomain hashCountCell
    small code entrySlices heapGlobal scratchGlobal frameGlobal aligned heapBound arena heapArena inputBeforeHeap arrayBeforeHeap
    frameReserve capReserve inputLimit inputBound limitBound orderedFrame framePositive scratchBelow countLimit
    (by change _ ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "is_valid_versioned_hashes") =
      some ([(ofString "si",.one)],sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes,.one) := by
    rw [code]; exact originalRuntimeCode_versionedHashes_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "is_valid_versioned_hashes") (ofString "si")
    (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) si installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "is_valid_versioned_hashes") destination arguments _
      (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock ≤ post.clock + (1 + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1))
      change state.clock - 1 ≤ post.clock + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) at spent
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock
      change post.clock ≤ state.clock - 1 at remaining
      omega

#print axioms evaluate_versioned_hashes_call_bounded
end InitECandidate.Runtime
