import InitECandidate.Runtime.ValidateHeadersParentCarry
import InitECandidate.Runtime.DecodeHeaderZeroFlag
/-!
The validation loop's parent carry, derived from the actual header decoder run.

`validate_headers_parent_carry` takes the root word as a hypothesis.  Here the root word
is derived from the actual `decode_header` body run through the zero-entry decoder
contract: the callee entry facts are the ones the loop's call establishes, the body run
is the actual one, and the returned record is the word the call binds to `h`.  So the
carry is a consequence of the frozen validation loop and the frozen decoder alone.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The validation loop's decode call carries the decoded parent header record, with the
root word coming from the actual decoder run rather than from a hypothesis. -/
theorem validate_headers_parent_carry_from_entry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (record : BitVec 64)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (lookup : lookupCodeHOLFinite s.code.lookup (ofString "decode_header")
      [.val (.word pointer),.val (.word length)] =
        some (sourceFunctionBody Guest.guestFn_decode_header, callee, returnShape))
    (clock : s.clock ≠ 0)
    (entryPointer : (callEntryStateHOLFinite s callee).locals.lookup (ofString "p") =
      some (.val (.word pointer)))
    (entryLength : (callEntryStateHOLFinite s callee).locals.lookup (ofString "len") =
      some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : (callEntryStateHOLFinite s callee).globals.lookup (ofString "scratch_ptr") =
      some (.val (.word scratch)))
    (frameGlobal : (callEntryStateHOLFinite s callee).globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling →
      (callEntryStateHOLFinite s callee).memaddrs address)
    (heap : (callEntryStateHOLFinite s callee).globals.lookup (ofString "heap_ptr") =
      some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 →
      (callEntryStateHOLFinite s callee).memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerPrefixCost inputLimit + headerWholeBodyCost inputLimit ≤
      (callEntryStateHOLFinite s callee).clock)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (decodeHeaderAt 0) =
      (some (.returned (.val (.word record))),post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite s callee).clock)
    (declared : shapeEqHOL (shapeOfHOLExact (.val (.word record))) .one = true)
    (returned : shapeEqHOL (shapeOfHOLExact (.val (.word record))) returnShape = true) :
    evaluateHOLFiniteState s validateHeadersFirstBody = validateHeadersTailRun s post record ∧
      (validateHeadersContinuation s post record).locals.lookup (ofString "h") = some (.val (.word record)) ∧
      ∃ rooted : BitVec 64, (validateHeadersContinuation s post record).memory (record + 32#64) = .word rooted := by
  obtain ⟨count,flag,decoded,decodedValue,countTwentyOne,currentBound,heapPost,⟨rooted,rootMem⟩,domainPost,
    codePost,scratchPost,framePost,beforePost,recordFitsPost,_,_⟩ :=
    decode_header_returned_root_from_zero (callEntryStateHOLFinite s callee) post pointer length scratch frame array
      ceiling inputLimit entryPointer entryLength noWrap lengthBound limitBound scratchGlobal frameGlobal
      (code.trans (by rfl)) orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      ceilingAligned inputAfter inputBeforeArray budget (.val (.word record)) bodyRun
  have same : decoded = record := by
    have value : (ValueHOL.val (HolWordLab.word record) : ValueHOL 64) = ValueHOL.val (HolWordLab.word decoded) :=
      decodedValue
    exact HolWordLab.word.inj (ValueHOL.val.inj value.symm)
  have rootHere : post.memory (record + 32#64) = .word rooted := by
    rw [← same]
    exact rootMem
  obtain ⟨body,hLocal,rootAt⟩ := validate_headers_parent_carry s post array index pointer length input
    inputLength callee returnShape record rooted atArray atIndex entry lookup clock bodyRun remaining declared
    returned rootHere
  exact ⟨body,hLocal,rooted,rootAt⟩

#print axioms validate_headers_parent_carry_from_entry
end InitECandidate.Runtime
