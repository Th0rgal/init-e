import InitECandidate.Runtime.ValidateHeadersBodyComposition
import InitECandidate.Runtime.ValidateHeadersSecondPhaseBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def validateHeadersBodyCost (inputLimit : Nat) : Nat := 4 + validateHeadersFirstLoopCost inputLimit + 33280

/-- All outcomes of the actual full function are bounded from the real
input witness and explicit entry workspace/heap geometry. No count cap,
buffer bound or callee runtime bound is assumed at function entry. -/
theorem runBounded_validate_headers_body {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : validateHeadersBodyCost inputLimit ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_validate_headers) (validateHeadersBodyCost inputLimit) := by
  apply runBounded_validate_headers_with_second_phase s array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit 33280
    inputBound inputCap inputAfter tableAbove tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    atArray atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget
  intro e next arrayEq countEq inputEq lengthEq limitEq hsEq hashEq invariant installed remaining
  obtain ⟨index,nextHeap,arr,n,i,hs,hashes,rest⟩ := invariant
  exact runBounded_validate_headers_second_phase next e.count index i n e.cap (installed.trans code) remaining

/-- Complete original header-validation source budget, including both
allocations, both loops and the final return. -/
theorem validateHeadersBodyCost_polynomial (limit : Nat) :
    validateHeadersBodyCost limit = 222720 * limit * limit + 260608 * limit + 664303108 := by
  simp only [validateHeadersBodyCost,validateHeadersFirstLoopCost_polynomial]
  ring

#print axioms runBounded_validate_headers_body
#print axioms validateHeadersBodyCost_polynomial
end InitECandidate.Runtime
