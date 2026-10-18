import InitECandidate.Runtime.TransactionU256FieldHeapOuterPrefix
import InitECandidate.Runtime.PanSeqAssoc
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned scalar/store/return suffix retains an independently bounded earlier slice array. -/
theorem transaction_u256_field_returned_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + offset.toNat + 24 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
        (.seq (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))
          (.return (.var .local (ofString "tx"))))) = (some (.returned value),post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let field : ProgHOL 64 := .seq
    (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
    (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))
  rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780] at run
  have noReturn := evaluate_noDirectReturn field (by rfl) state value
  cases fieldRun : evaluateHOLFiniteState state field with
  | mk result middle =>
    dsimp only [field] at fieldRun noReturn
    rw [fieldRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have kept := transaction_u256_field_normal_heap_outer_prefix state middle tx offset arguments
        array index maximum input inputLength scratch frame count ceiling inputLimit args valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove txLocal before fits fieldRun
      have memory := evaluate_readOnly_memory (.return (.var .local (ofString "tx"))) (by rfl) middle
      have metadata := evaluateHOLFiniteState_metadata middle (.return (.var .local (ofString "tx")))
      dsimp only at run
      rw [run] at memory metadata
      intro slot within
      obtain ⟨p,n,item⟩ := kept slot within
      exact ⟨p,n,item.after_frame middle post outerArray slot p n outerInput outerLength metadata.2.1
        (congrFun memory _) (congrFun memory _)⟩

#print axioms transaction_u256_field_returned_heap_outer_prefix
end InitECandidate.Runtime
