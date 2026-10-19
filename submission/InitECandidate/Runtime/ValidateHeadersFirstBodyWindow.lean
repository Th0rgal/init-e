import InitECandidate.Runtime.ValidateHeadersFirstBodyBound
import InitECandidate.Runtime.ValidateHeadersFirstTailNormalFrame
import InitECandidate.Runtime.ValidateHeadersFirstIndexProgress
import InitECandidate.Runtime.ReachesNormalContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Successful original first-loop iterations keep the decoder workspace,
real witness prefix and heap ordering, and increment the actual caller index. -/
theorem validate_headers_first_body_window {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (budget : headerDecoderBodyCost inputLimit + 1 + (inputLimit * 20 + 125) ≤ s.clock)
    (hsBeforeHashes : hs.toNat ≤ hashes.toNat)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (hsBeforeHeap : hs.toNat ≤ heap.toNat)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < hs.toNat → post.memory address = s.memory address) := by
  have decoded := validate_headers_decode_reaches s array count index pointer length input inputLength scratch frame heap ceiling inputLimit
    atArray atIndex entry table inputBound inputAfter inputBeforeHeap tableAbove tableBefore limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heapGlobal heapBound countLimit heapArena ceilingAligned (by omega)
  obtain ⟨ready,facts,remaining,agreement,tailNormal⟩ := reaches_normal_continuation_budget s validateHeadersFirstBody validateHeadersFirstTail _
    (headerDecoderBodyCost inputLimit + 1) (inputLimit * 20 + 125) decoded budget (by rw [normal])
  obtain ⟨fieldCount,fieldBound,fieldCap,locals,recordAfter,heapNext,scratchNext,frameNext,domain,installed,recordEnd,heapEnd,heapAligned,memory,tableNext,workspace⟩ := facts
  have lookupKept (name : MlS) (different : name ≠ ofString "h") : ready.locals.lookup name = s.locals.lookup name := by
    rw [locals]
    simp [FUPDATE,different,Ne.symm different]
  let tailPost := (evaluateHOLFiniteState ready validateHeadersFirstTail).2
  have tailRun : evaluateHOLFiniteState ready validateHeadersFirstTail = (none,tailPost) := by
    exact Prod.ext tailNormal rfl
  obtain ⟨tailTable,tailLocals,tailGlobals,tailDomain,tailCode,tailMemory,progress⟩ :=
    validate_headers_first_tail_normal_frame ready tailPost array count index input inputLength hs hashes
      (allocationEnd heap (fieldCount * 16)) keccakState keccakPad inputLimit ceiling
      ((lookupKept _ (by decide)).trans atArray) ((lookupKept _ (by decide)).trans atIndex)
      ((lookupKept _ (by decide)).trans atHs) ((lookupKept _ (by decide)).trans atHashes)
      (by rw [locals]; simp [FUPDATE]) inside tableNext tableBeforeHs hsBufferBound hashBufferBound hashAligned inputBound inputCap
      (by rw [workspace _ (by decide)]; exact stateGlobal) (by rw [workspace _ (by decide)]; exact padGlobal)
      (installed.trans code) remaining tableAbove hsBeforeHashes stateBelow padBelow tailRun
  rw [normal,tailRun] at agreement
  have memoryEq : post.memory = tailPost.memory := agreement.2.2.1
  intro address lo hi
  rw [memoryEq]
  exact (tailMemory address lo hi).trans (memory address lo (by omega))

#print axioms validate_headers_first_body_window
end InitECandidate.Runtime
