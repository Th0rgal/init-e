import InitECandidate.Runtime.RlpValidationPublicCallAbove
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original RLP validation preserves an independent heap slice array
above its scratch ceiling. No reserve placing heap arrays below frame_mem_ptr
is required: scratch records descend below the protected array. -/
theorem rlpValidation_call_normal_heap_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 5 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_validate_items") arguments) = (none,post))
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) (above : ceiling ≤ array.toNat) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "rlp_validate_items") arguments)
  rw [run] at metadata
  apply RlpSliceInputPrefix.after_memory_above state post array count input inputLength valid fits metadata.2.1
  intro address aboveArray
  exact rlpValidation_call_normal_above state post arguments pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run address (by omega)

#print axioms rlpValidation_call_normal_heap_prefix
end InitECandidate.Runtime
