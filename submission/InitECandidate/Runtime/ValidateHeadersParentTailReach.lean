import InitECandidate.Runtime.ValidateHeadersParentCarryEntry
/-!
The validation loop's decode call as a reach into its own tail.

The loop body of the frozen validation source is the decode call followed by the tail.
This module states that composition in the reach form: from the loop's state, the body
reaches a state (the continuation the frozen call semantics builds) in which the parent
record pointer is bound to `h`, the record's root word is readable at `record + 32`, the
domain, memory, globals and clock are the callee's, and the allocated record extent stays
under the heap cap.  From that state the tail runs, so the record is carried into the
tail's execution rather than assumed in an equality.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The validation loop's decode call reaches its tail with the decoded parent record
carried: `h` holds the record pointer, the root word is readable at `record + 32`, the
record extent stays under the heap cap, and the continuation keeps the callee's memory,
globals, domain and clock. -/
theorem validate_headers_parent_tail_reaches {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (returned : shapeEqHOL (shapeOfHOLExact (.val (.word record))) returnShape = true)
    (extent : (allocationEnd record 248).toNat ≤ 33806089496)
    (used : s.clock ≤ post.clock + (headerPrefixCost inputLimit + headerWholeBodyCost inputLimit + 2)) :
    Reaches s validateHeadersFirstBody
      (fun ready => ready.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        (∃ rooted : BitVec 64, ready.memory (record + 32#64) = .word rooted) ∧
        ready.clock = post.clock ∧ ready.memory = post.memory ∧ ready.globals = post.globals ∧
        ready.memaddrs = post.memaddrs ∧ (allocationEnd record 248).toNat ≤ 33806089496)
      (headerPrefixCost inputLimit + headerWholeBodyCost inputLimit + 2) validateHeadersFirstTail := by
  obtain ⟨body,hLocal,rooted,rootAt⟩ := validate_headers_parent_carry_from_entry s post array index pointer
    length input inputLength scratch frame ceiling inputLimit callee returnShape record atArray atIndex entry lookup
    clock entryPointer entryLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena heap arrayBound countLimit heapArena ceilingAligned inputAfter inputBeforeArray
    budget bodyRun remaining declared returned
  have newClock : (validateHeadersContinuation s post record).clock = post.clock := by
    simp [validateHeadersContinuation,setVarHOLFinite]
  have newMemory : (validateHeadersContinuation s post record).memory = post.memory := by
    simp [validateHeadersContinuation,setVarHOLFinite]
  have newGlobals : (validateHeadersContinuation s post record).globals = post.globals := by
    simp [validateHeadersContinuation,setVarHOLFinite]
  have newDomain : (validateHeadersContinuation s post record).memaddrs = post.memaddrs := by
    simp [validateHeadersContinuation,setVarHOLFinite]
  refine Or.inl ⟨validateHeadersContinuation s post record,
    ⟨hLocal,⟨rooted,rootAt⟩,newClock,newMemory,newGlobals,newDomain,extent⟩,?_,?_,?_⟩
  · rw [newClock]
    omega
  · rw [newClock]
    have entryClock : (callEntryStateHOLFinite s callee).clock ≤ s.clock := by
      simp [callEntryStateHOLFinite]
    omega
  · rw [body]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms validate_headers_parent_tail_reaches
end InitECandidate.Runtime
