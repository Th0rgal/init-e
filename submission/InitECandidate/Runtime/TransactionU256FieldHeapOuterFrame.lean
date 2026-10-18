import InitECandidate.Runtime.TransactionU256FieldHeapPrefix
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.TransactionU256FieldHeapOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A complete scalar field retains globals, input slices and all other caller locals. -/
theorem transaction_u256_field_normal_heap_outer_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx offset : BitVec 64) (arguments : List (ExpHOL 64))
    (array index maximum input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + offset.toNat + 24 < array.toNat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
        (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))) = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ other, other ≠ ofString "v" → post.locals.lookup other = state.locals.lookup other) := by
  have slices := transaction_u256_field_normal_heap_prefix state post tx offset arguments array index maximum input inputLength scratch frame count ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove txLocal before run
  have outer := transaction_u256_field_normal_heap_outer_prefix state post tx offset arguments array index maximum input inputLength scratch frame count ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
    outerArray outerCount outerInput outerLength outerValid outerFits outerAbove txLocal beforeTx (Nat.lt_trans before array.isLt) run
  refine ⟨slices,outer,?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some result => cases run
    | none =>
      have retained := txScalarU256_local_call_normal_heap_frame state middle (ofString "v") arguments array index maximum input inputLength scratch frame count ceiling inputLimit
        args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove callRun
      have other := evaluate_local_call_success_other_locals state (ofString "tx_scalar_u256") (ofString "v") arguments (by rw [callRun])
      dsimp only at run
      have storeLocals := (evaluate_store_control_frame middle
        (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v"))).2.1
      rw [run] at storeLocals
      refine ⟨?_,?_⟩
      · intro watched
        have globals := evaluate_avoidsGlobalAssignment watched
          (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v"))) (by rfl) middle
        rw [run] at globals
        exact globals.trans (retained.1 watched)
      · intro watched different
        have same := other watched different
        rw [callRun] at same
        rw [storeLocals]
        exact same

#print axioms transaction_u256_field_normal_heap_outer_frame
end InitECandidate.Runtime
