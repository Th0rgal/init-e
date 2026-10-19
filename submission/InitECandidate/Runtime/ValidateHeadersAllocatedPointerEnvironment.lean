import InitECandidate.Runtime.ValidateHeadersAllocatedReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 400000

/-- Construct the loop environment from real allocation extents rather than
assuming bounded or separated header buffers at entry. -/
theorem validate_headers_allocated_pointer_environment {F : Type} (s first post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (cap : count.toNat ≤ 256) (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (hsAllocation : AllocationDeclarationReady s (ofString "hs") heap (validateHeadersHsSize count) first)
    (hashAllocation : AllocationDeclarationReady first (ofString "hashes") (allocationEnd heap (validateHeadersHsSize count))
      (validateHeadersHashesSize count) post) :
    ∃ e : ValidateHeadersFirstEnvironment,
      e.array = array ∧ e.count = count ∧ e.input = input ∧ e.inputLength = inputLength ∧ e.inputLimit = inputLimit ∧
      e.hs = heap ∧ e.hashes = allocationEnd heap (validateHeadersHsSize count) ∧
      ValidateHeadersFirstReady e post ∧ post.code = s.code ∧
      e.ceiling = ceiling ∧ e.scratch = scratch ∧ e.frame = frame ∧ e.keccakState = keccakState ∧ e.keccakPad = keccakPad ∧
      e.ceiling ≤ e.hs.toNat ∧ e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat ∧
      (∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        e.hs.toNat + e.count.toNat * 8 ≤ finalHeap.toNat) := by
  obtain ⟨hs,hashes,n,heapGlobal,memory,domain,installed,hsExtent,hashExtent,hashAligned,heapAligned,heapBound,globals⟩ :=
    validate_headers_buffers s first post count heap cap atCount hsAllocation hashAllocation
  let e : ValidateHeadersFirstEnvironment := {
    array := array, count := count, input := input, inputLength := inputLength,
    scratch := scratch, frame := frame, hs := heap, hashes := allocationEnd heap (validateHeadersHsSize count),
    keccakState := keccakState, keccakPad := keccakPad, ceiling := ceiling, inputLimit := inputLimit,
    cap := cap, inputBound := inputBound, inputCap := inputCap, inputAfter := inputAfter, tableAbove := tableAbove,
    tableBeforeHs := tableBefore, hsBufferBound := by omega, hashBufferBound := by omega,
    hashAligned := hashAligned, hsBeforeHashes := by omega, orderedFrame := orderedFrame,
    framePositive := framePositive, scratchBelow := scratchBelow, ceilingAligned := ceilingAligned,
    stateBelow := stateBelow, padBelow := padBelow }
  obtain ⟨ready,code⟩ := validate_headers_allocated_ready e s first post atArray atCount table inputBefore
    scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena rfl hsAllocation hashAllocation
  refine ⟨e,rfl,rfl,rfl,rfl,rfl,rfl,rfl,ready,code,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · dsimp only [e]; omega
  · dsimp only [e]; omega
  · exact ⟨allocationEnd (allocationEnd heap (validateHeadersHsSize count)) (validateHeadersHashesSize count),
      heapGlobal,by dsimp only [e]; omega⟩

#print axioms validate_headers_allocated_pointer_environment
end InitECandidate.Runtime
