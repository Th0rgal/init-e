import InitECandidate.Runtime.ValidateHeadersParentReaches
/-!
The validation loop's decode call as a named reach, with the caller's own table retained.

`validate_headers_parent_reaches` states the call's reach with `parentRecordCarry s · ...`, an
anonymous lambda.  Downstream loop work has to name that predicate to keep the reach small and
readable, so this module introduces `StoredRootsParentCarry` and restates the existing theorem
with it, fixing the retained outer witness prefix to the caller's own slice-witness table: the
call is entered with a table that is already above the ceiling and below the heap, so the table
itself is the prefix the carry hands to the next stage.

Nothing about the decoder is reproved and nothing is assumed: this is the existing checked reach,
specialised to the table the loop actually holds.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The decode call's carry as a named predicate: the parent record the loop's header decoder
returns, with the caller's slice-witness table kept as the retained outer prefix. -/
def StoredRootsParentCarry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (heap pointer length : BitVec 64) (ceiling : Nat)
    (array input inputLength count : BitVec 64) : PanSemStateFiniteExact 64 F → Prop :=
  fun next => parentRecordCarry s next heap pointer length ceiling array input inputLength count

/-- The loop's actual header-decode call reaches its tail satisfying the named carry
`StoredRootsParentCarry`, with the caller's own table as the retained outer witness prefix. -/
theorem validate_headers_stored_roots_parent_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array heapStart index pointer length input inputLength scratch frame count : BitVec 64)
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
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (tableAbove : ceiling ≤ array.toNat) (tableBefore : array.toNat + count.toNat * 16 ≤ heapStart.toNat)
    (budget : headerDecoderBodyCost inputLimit + 2 ≤ s.clock) :
    Reaches s validateHeadersFirstBody
      (StoredRootsParentCarry s heapStart pointer length ceiling array input inputLength count)
      (headerDecoderBodyCost inputLimit + 1) validateHeadersFirstTail :=
  validate_headers_parent_reaches s array heapStart index pointer length input inputLength scratch frame
    array count input inputLength ceiling inputLimit atArray atIndex entry noWrap lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heapGlobal heapCapped
    countLimit heapArena ceilingAligned inputAfter inputBeforeHeap table tableAbove tableBefore budget

#print axioms validate_headers_stored_roots_parent_reaches
end InitECandidate.Runtime
