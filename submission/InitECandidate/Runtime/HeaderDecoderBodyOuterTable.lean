import InitECandidate.Runtime.HeaderDecoderBodyReturnedContract
import InitECandidate.Runtime.RlpSliceInputPrefixBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A successful original header decode retains the actual older witness
slice array while returning its allocated record and bounded restored workspace. -/
theorem header_decoder_body_returned_outer_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerDecoderBodyCost inputLimit ≤ s.clock)
    (older olderCount outerInput outerLength : BitVec 64)
    (olderTable : RlpSliceInputPrefix s older outerInput outerLength olderCount.toNat)
    (olderAbove : ceiling ≤ older.toNat)
    (olderBefore : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_header) = (some (.returned value),post)) :
    ∃ count : BitVec 64,
      count.toNat ≤ length.toNat ∧ count.toNat ≤ 23 ∧ value = .val (.word (allocationEnd array (count * 16))) ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (allocationEnd array (count * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd array (count * 16)) 248).toNat ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → post.memory address = s.memory address) ∧
      RlpSliceInputPrefix post older outerInput outerLength olderCount.toNat := by
  obtain ⟨count,countBound,countSmall,valueEq,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory⟩ :=
    header_decoder_body_returned_contract s post pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      ceilingAligned inputAfter inputBeforeArray budget value run
  refine ⟨count,countBound,countSmall,valueEq,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory,?_⟩
  exact olderTable.after_memory_between s post older olderCount outerInput outerLength array ceiling olderAbove olderBefore domain
    (fun address hi lo => memory address lo hi)

#print axioms header_decoder_body_returned_outer_table
end InitECandidate.Runtime
