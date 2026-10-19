import InitECandidate.Runtime.HeaderDecoderBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The installed original decoder call adds exactly one entry tick to the
whole-body bound, with explicit input/workspace/initial-heap caller premises. -/
theorem runBounded_decode_header_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
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
    (budget : headerDecoderBodyCost inputLimit + 1 ≤ s.clock) : RunBounded s (.call (some (destination,none)) (ofString "decode_header") arguments)
      (headerDecoderBodyCost inputLimit + 1) := by
  apply RunBounded.call (bodyCost := headerDecoderBodyCost inputLimit) args budget
  intro body callee shape lookup
  have installed := pan_two_word_lookup_shape s.code.lookup (ofString "decode_header") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_header) .one pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeHeader_lookup)
  rw [installed] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  exact runBounded_decode_header_body entry pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    ceilingAligned inputAfter inputBeforeArray (by change headerDecoderBodyCost inputLimit ≤ s.clock - 1; omega)

#print axioms runBounded_decode_header_call
end InitECandidate.Runtime
