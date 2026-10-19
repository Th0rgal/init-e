import InitECandidate.Runtime.HeaderDecoderFieldsBound
import InitECandidate.Runtime.DecodeHeaderInitialFieldsReach
import InitECandidate.Runtime.AllocationRoundNoWrap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def headerDecoderBodyCost (limit : Nat) : Nat :=
  (decodeHeaderRlpCost limit + decodeHeaderSlicesCost limit + 2) + 27 * headerDecoderUnitCost limit

/-- The complete original header decoder, from its first parse through its
actual return, has a uniform finite input-quadratic source runtime bound.
The workspace, input and initial heap premises are explicit caller obligations. -/
theorem runBounded_decode_header_body {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : headerDecoderBodyCost inputLimit ≤ s.clock) : RunBounded s (sourceFunctionBody Guest.guestFn_decode_header) (headerDecoderBodyCost inputLimit) := by
  have first := decode_header_initial_fields_reaches s pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    ceilingAligned inputAfter inputBeforeArray (by unfold headerDecoderBodyCost at budget; omega)
  rw [source_decode_header_body]
  unfold headerDecoderBodyCost at budget ⊢
  apply RunBounded.ofReaches budget first
  intro ready facts remaining
  obtain ⟨count,flag,countBound,accepted,arr,n,flagLocal,header,table,heapBinding,scratchBinding,frameBinding,
    domain,installed,extent,cap,aligned⟩ := facts
  have countSmall : count.toNat ≤ 23 := by
    rcases accepted with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have sizeNat : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have before : array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat := by
    have covers := allocationEnd_covers_noWrap array (count * 16) (by rw [sizeNat]; omega)
    simpa only [sizeNat] using covers
  have g : HeaderDecoderGeometry array count length scratch frame (allocationEnd array (count * 16)) flag ceiling inputLimit :=
    ⟨before,by omega,by omega,by omega,lengthBound,limitBound,orderedFrame,framePositive,scratchBelow,accepted⟩
  have c : HeaderDecoderContext ready array count pointer length scratch frame (allocationEnd array (count * 16)) flag ceiling :=
    ⟨arr,header,flagLocal,table,scratchBinding,frameBinding,installed.trans code,by
      intro address lo hi
      rw [domain]
      exact arena address lo hi⟩
  exact header_decoder_at9_bounded ready array count pointer length scratch frame (allocationEnd array (count * 16)) flag ceiling inputLimit g c remaining

#print axioms runBounded_decode_header_body
end InitECandidate.Runtime
