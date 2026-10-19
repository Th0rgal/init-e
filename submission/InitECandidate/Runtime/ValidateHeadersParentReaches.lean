import InitECandidate.Runtime.ValidateHeadersParentCarry
import InitECandidate.Runtime.HeaderDecoderBodyBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.PanTwoWordShapeLookup
/-!
The validation loop's decode call reaches its own tail with the decoded parent record.

The loop body is the actual `.decCall (ofString "h") .one (ofString "decode_header")
validateHeadersDecodeArguments validateHeadersFirstTail`.  Two different arrays appear at the
call site and they are kept apart:

* `array` is the caller's slice-witness table, read only by the argument evaluation;
* `heapStart` is the value of `heap_ptr` at the call, i.e. the allocator array the header
  decoder hands to its own allocation.

The call is closed by `bounded_decCall_reaches` from the real all-outcome body bound
`runBounded_decode_header_body`, the installed lookup is derived by
`pan_two_word_lookup_shape` from `originalRuntimeCode_decodeHeader_lookup`, and the returned
record is the actual record of `decode_header_returned_root_from_zero`: it is
`allocationEnd heapStart (count * 16)` for a count of twenty-one or twenty-three fields, its
generated state root word is readable at `record + 32`, and that word's address is inside the
arena the caller already justifies.

The room premise `heapCapped` is an explicit interim invariant: the heap at the call has room
for the largest header record.  It is stated on `heapStart` only, so it says nothing about the
caller's slice table.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The heap room the interim carry invariant asks for: the largest header record (23 fields,
368 bytes) rounded up to 376, the 248 bytes of its state-root allocation and the 32-byte root
window all fit below the heap cap. -/
def headerCarryRoom : Nat := 624

/-- The complete decoder body bound dominates the prefix reach and the returned-root suffix
budget that the returned-header contract needs. -/
theorem header_prefix_whole_le_body (inputLimit : Nat) :
    headerPrefixCost inputLimit + headerWholeBodyCost inputLimit ≤ headerDecoderBodyCost inputLimit := by
  simp only [headerPrefixCost, headerWholeBodyCost, headerWholeFieldCost, headerDecoderSpanCost,
    headerDecoderUnitCost, headerDecoderBodyCost, headerRlpFieldCost]
  omega

/-- The validation loop's actual header-decode call reaches the loop tail with the decoded
parent record bound to `h`, the record's generated state root word readable at `record + 32`
and inside the caller's arena, and the record extent below the heap cap.  Nothing about the
callee's execution is assumed: the body run, its bound and the installed lookup are all
derived from the entry invariants. -/
theorem validate_headers_parent_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array heapStart index pointer length input inputLength scratch frame : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heapStart)))
    (heapCapped : heapStart.toNat + headerCarryRoom ≤ 33806089496)
    (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapStart.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeHeap : pointer.toNat + length.toNat ≤ heapStart.toNat)
    (budget : headerDecoderBodyCost inputLimit + 2 ≤ s.clock) :
    Reaches s validateHeadersFirstBody
      (fun next => ∃ value : ValueHOL 64, ∃ post : PanSemStateFiniteExact 64 F,
        ∃ count record rooted : BitVec 64,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (rlpHeaderCallee pointer length)) (decodeHeaderAt 0) =
          (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) .one = true ∧
        value = .val (.word record) ∧
        record = allocationEnd heapStart (count * 16) ∧
        next = validateHeadersContinuation s post record ∧
        next.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        next.memory (record + 32#64) = .word rooted ∧
        next.memaddrs (record + 32#64) ∧
        next.memaddrs = s.memaddrs ∧ next.code = s.code ∧
        next.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (allocationEnd (allocationEnd heapStart (count * 16)) 248))) ∧
        next.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
        next.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr") ∧
        heapStart.toNat + 21 * 16 ≤ record.toNat ∧ record.toNat + 248 ≤ 33806089496)
      (headerDecoderBodyCost inputLimit + 1) validateHeadersFirstTail := by
  let entryState := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have args := eval_validate_headers_decode_arguments s array index pointer length input inputLength atArray
    atIndex entry
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "decode_header") (ofString "p")
    (ofString "len") (sourceFunctionBody Guest.guestFn_decode_header) .one pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeHeader_lookup)
  have p : entryState.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entryState,callEntryStateHOLFinite,rlpHeaderCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have len : entryState.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entryState,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have room : heapStart.toNat + 624 ≤ 33806089496 := by
    simpa only [headerCarryRoom] using heapCapped
  have bodyBudget : headerDecoderBodyCost inputLimit ≤ entryState.clock := by
    change headerDecoderBodyCost inputLimit ≤ s.clock - 1
    omega
  have contractBudget : headerPrefixCost inputLimit + headerWholeBodyCost inputLimit ≤ entryState.clock := by
    have link := header_prefix_whole_le_body inputLimit
    change headerPrefixCost inputLimit + headerWholeBodyCost inputLimit ≤ s.clock - 1
    omega
  have bounded := runBounded_decode_header_body entryState pointer length scratch frame heapStart ceiling
    inputLimit p len noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena heapGlobal (by omega) countLimit heapArena
    ceilingAligned inputAfter inputBeforeHeap bodyBudget
  rw [source_validate_headers_first_decode]
  apply bounded_decCall_reaches s (ofString "h") (ofString "decode_header") .one .one
    validateHeadersDecodeArguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_decode_header) validateHeadersFirstTail (rlpHeaderCallee pointer length)
    (headerDecoderBodyCost inputLimit) _ args lookup (by omega) bounded
  intro value post run checked
  have contract := decode_header_returned_root_from_zero entryState post pointer length scratch frame heapStart
    ceiling inputLimit p len noWrap lengthBound limitBound scratchGlobal frameGlobal (code.trans (by rfl))
    orderedFrame framePositive scratchBelow arena heapGlobal (by omega)
    countLimit heapArena ceilingAligned inputAfter inputBeforeHeap contractBudget value
    (by simpa only [source_decode_header_body] using run)
  obtain ⟨count,flag,record,valueEq,countTwentyOne,countBound,heapPost,⟨rooted,rootMem⟩,domainPost,codePost,
    scratchPost,framePost,beforePost,_,recordEq,startCap⟩ := contract
  have sizeNat : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have roomBound : heapStart.toNat + (count * 16).toNat ≤ 33806089496 := by
    rw [sizeNat]
    have small : count.toNat * 16 ≤ 368 := by omega
    omega
  have covered := allocationEnd_covers heapStart (count * 16) roomBound
  have recordBelow : record.toNat < heapStart.toNat + (count * 16).toNat + 8 := by
    rw [recordEq]
    exact covered.2.1
  have recordInside : record.toNat + 248 ≤ 33806089496 := by
    rw [sizeNat] at recordBelow
    omega
  have rootAddr : (record + 32#64).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 32 < 2^64; omega)]
    rfl
  have rootInside : (record + 32#64).toNat < 33806089496 := by
    rw [rootAddr]
    omega
  let continuation := validateHeadersContinuation s post record
  have hLocal : continuation.locals.lookup (ofString "h") = some (.val (.word record)) := by
    simp [continuation,validateHeadersContinuation,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  refine ⟨value,post,count,record,rooted,(by simpa only [source_decode_header_body] using run),checked.1,
    valueEq,recordEq,?_,?_,?_,?_,?_,?_,?_,?_,?_,beforePost,recordInside⟩
  · rw [valueEq]
    rfl
  · rw [valueEq]
    exact hLocal
  · rw [valueEq]
    change post.memory (record + 32#64) = .word rooted
    exact rootMem
  · rw [valueEq]
    change post.memaddrs (record + 32#64)
    rw [domainPost]
    exact heapArena (record + 32#64) (by rw [rootAddr]; omega) rootInside
  · rw [valueEq]
    change post.memaddrs = s.memaddrs
    exact domainPost
  · rw [valueEq]
    change post.code = s.code
    exact codePost
  · rw [valueEq]
    change post.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd (allocationEnd heapStart (count * 16)) 248)))
    exact heapPost
  · rw [valueEq]
    change post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr")
    exact scratchPost
  · rw [valueEq]
    change post.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr")
    exact framePost

#print axioms validate_headers_parent_reaches
end InitECandidate.Runtime
