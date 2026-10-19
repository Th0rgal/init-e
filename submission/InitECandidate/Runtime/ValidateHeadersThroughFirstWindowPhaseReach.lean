import InitECandidate.Runtime.ValidateHeadersAllocatedEnvironment
import InitECandidate.Runtime.ValidateHeadersFirstWindowPhaseReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual count guard, both allocations, index initialization and whole
first loop reach the second phase within a concrete input-dependent budget. -/
theorem validate_headers_through_first_window_phase_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
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
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : 4 + validateHeadersFirstLoopCost inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 0)
      (fun post => ∃ e : ValidateHeadersFirstEnvironment,
        e.array = array ∧ e.count = count ∧ e.input = input ∧ e.inputLength = inputLength ∧ e.inputLimit = inputLimit ∧
        e.hs = heap ∧ e.hashes = allocationEnd heap (validateHeadersHsSize count) ∧
        ValidateHeadersFirstWindowInvariant e s.memory post 0 ∧ post.code = s.code)
      (4 + validateHeadersFirstLoopCost inputLimit) (validateHeadersAt 5) := by
  have allocated := validate_headers_prefix_reaches s count heap code atCount heapGlobal heapBound (by omega)
  apply reaches_trans_budget s (validateHeadersAt 0) (validateHeadersAt 3) (validateHeadersAt 5) _ _
    4 (validateHeadersFirstLoopCost inputLimit) budget allocated
  intro ready facts remaining
  obtain ⟨cap,first,hsAllocation,hashAllocation⟩ := facts
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,prepared,installed⟩ :=
    validate_headers_allocated_environment s first ready array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
      cap inputBound inputCap inputAfter tableAbove tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
      atArray atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena hsAllocation hashAllocation
  obtain ⟨hsLocal,hashLocal,countLocal,finalHeapGlobal,memory,domain,codeKept,hsExtent,hashExtent,hashAligned,heapAligned,finalHeapBound,globals⟩ :=
    validate_headers_buffers s first ready count heap cap atCount hsAllocation hashAllocation
  have heapLower : ∃ finalHeap : BitVec 64, ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧ heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 :=
    ⟨allocationEnd (allocationEnd heap (validateHeadersHsSize count)) (validateHeadersHashesSize count),finalHeapGlobal,⟨by omega,heapAligned⟩⟩
  have phase := validate_headers_first_window_phase_reaches e s.memory ready (installed.trans code) prepared (by rw [hsEq]; exact heapLower) (fun address _ _ => congrFun memory address) (by rw [limitEq]; exact remaining)
  rw [limitEq] at phase
  exact reaches_mono ready (validateHeadersAt 3) (validateHeadersAt 5) _ _ _ _ (le_refl _)
    (fun post result => ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,result.1,result.2.trans installed⟩) phase

#print axioms validate_headers_through_first_window_phase_reaches
end InitECandidate.Runtime
