import InitECandidate.Runtime.TransactionTypedPathBelow
import InitECandidate.Runtime.TransactionTypeGuard
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_branch_normal_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionTypeParseBranch = (none,post)) (address : BitVec 64) (below : address.toNat < frame.toNat) :
    post.memory address = state.memory address := by
  have range := transaction_typed_decode_range pointer length positive inputRange
  have factor : (2 * (length - 1).toNat + 1) * 15 + 19 ≤ (2 * length.toNat + 1) * 15 + 19 := by omega
  have product := Nat.mul_le_mul range.2.2.2 factor
  have typedBudget : (length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92634 ≤ state.clock := by omega
  rw [source_transaction_type_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_ite] at run
      split at run
      · split at run
        · have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 2)
          rw [run] at terminal
          exact False.elim (terminal rfl)
        · exact transaction_legacy_path_normal_below state post pointer length scratch frame ceiling inputLimit
            pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run address below
      · cases run
    · exact transaction_typed_path_normal_below state post pointer length scratch frame ceiling inputLimit
        pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena typedBudget run address below
  · cases run

theorem transaction_type_branch_normal_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (run : evaluateHOLFiniteState state transactionTypeParseBranch = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeParseBranch
  rw [run] at metadata
  exact rlp_slice_input_prefix_after_lower_frame state post array count input inputLength frame valid before metadata.2.1
    (fun address below => transaction_type_branch_normal_below state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena budget run address below)

#print axioms transaction_type_branch_normal_input_prefix
#print axioms transaction_type_branch_normal_below
end InitECandidate.Runtime
