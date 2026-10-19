import InitECandidate.Runtime.ValidateHeadersDecodeReach
import InitECandidate.Runtime.ValidateHeadersFirstTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- All outcomes of the actual first validation-loop body, including failed accesses. -/
theorem runBounded_validate_headers_first_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count index pointer length input inputLength scratch frame heap hs hashes keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputAfter : ceiling ≤ input.toNat)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (tableAbove : ceiling ≤ array.toNat) (tableBefore : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0)
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (inside : index.toNat < count.toNat)
    (tableBeforeHs : array.toNat + count.toNat * 16 ≤ hs.toNat)
    (hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (inputCap : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (budget : headerDecoderBodyCost inputLimit + 1 + (inputLimit * 20 + 125) ≤ s.clock) :
    RunBounded s validateHeadersFirstBody (headerDecoderBodyCost inputLimit + 1 + (inputLimit * 20 + 125)) := by
  have decoded := validate_headers_decode_reaches s array count index pointer length input inputLength scratch frame heap ceiling inputLimit
    atArray atIndex entry table inputBound inputAfter inputBeforeHeap tableAbove tableBefore limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heapGlobal heapBound countLimit heapArena ceilingAligned (by omega)
  apply RunBounded.ofReaches budget decoded
  intro ready facts remaining
  obtain ⟨fieldCount,fieldBound,fieldCap,locals,recordAfter,heapNext,scratchNext,frameNext,domain,installed,recordEnd,heapEnd,heapAligned,memory,tableNext,workspace⟩ := facts
  have lookupKept (name : MlS) (different : name ≠ ofString "h") : ready.locals.lookup name = s.locals.lookup name := by
    rw [locals]
    simp [FUPDATE,different,Ne.symm different]
  have atArrayNext := lookupKept (ofString "arr") (by decide)
  have atIndexNext := lookupKept (ofString "i") (by decide)
  have atHsNext := lookupKept (ofString "hs") (by decide)
  have atHashesNext := lookupKept (ofString "hashes") (by decide)
  have atHeader : ready.locals.lookup (ofString "h") = some (.val (.word (allocationEnd heap (fieldCount * 16)))) := by
    rw [locals]
    simp [FUPDATE]
  apply runBounded_validate_headers_first_tail ready array count index input inputLength hs hashes
    (allocationEnd heap (fieldCount * 16)) keccakState keccakPad inputLimit
    (atArrayNext.trans atArray) (atIndexNext.trans atIndex) (atHsNext.trans atHs) (atHashesNext.trans atHashes)
    atHeader inside tableNext tableBeforeHs hsBufferBound hashBufferBound hashAligned inputBound inputCap
    (by rw [workspace (ofString "keccak_st") (by decide)]; exact stateGlobal)
    (by rw [workspace (ofString "keccak_pad") (by decide)]; exact padGlobal)
    (installed.trans code) remaining

#print axioms runBounded_validate_headers_first_body
end InitECandidate.Runtime
