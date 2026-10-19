import InitECandidate.Runtime.ValidateHeadersFirstSource
import InitECandidate.Runtime.HeaderDecoderDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The validation loop's actual header declaration consumes its readable
witness entry; input span geometry discharges the decoder's pointer/length premises. -/
theorem validate_headers_decode_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count index pointer length input inputLength scratch frame heap : BitVec 64) (ceiling inputLimit : Nat)
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
    (budget : headerDecoderBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s validateHeadersFirstBody
      (fun ready => ∃ fieldCount : BitVec 64,
      fieldCount.toNat ≤ length.toNat ∧ fieldCount.toNat ≤ 23 ∧ ready.locals = s.locals.update (ofString "h",.val (.word (allocationEnd heap (fieldCount * 16)))) ∧
      heap.toNat + fieldCount.toNat * 16 ≤ (allocationEnd heap (fieldCount * 16)).toNat ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd heap (fieldCount * 16)) 248))) ∧
      ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
      (allocationEnd heap (fieldCount * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd heap (fieldCount * 16)) 248).toNat ∧
      (allocationEnd (allocationEnd heap (fieldCount * 16)) 248).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd heap (fieldCount * 16)) 248).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat → ready.memory address = s.memory address) ∧
      RlpSliceInputPrefix ready array input inputLength count.toNat ∧
      (∀ global : MlS, global ∈ parserWorkspaceGlobals → ready.globals.lookup global = s.globals.lookup global))
      (headerDecoderBodyCost inputLimit + 1) validateHeadersFirstTail := by
  rw [source_validate_headers_first_decode]
  have args := eval_validate_headers_decode_arguments s array index pointer length input inputLength atArray atIndex entry
  have starts := entry.startsWithin
  have ends := entry.endsWithin
  exact header_decoder_declaration_reaches s pointer length scratch frame heap ceiling inputLimit (ofString "h") validateHeadersDecodeArguments args
    entry.noWrap ((entry.length_bound s array index pointer length input inputLength).trans inputBound) limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heapGlobal heapBound countLimit heapArena ceilingAligned (by omega) (by omega) budget
    array count input inputLength table tableAbove tableBefore validateHeadersFirstTail

#print axioms validate_headers_decode_reaches
end InitECandidate.Runtime
