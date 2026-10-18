import InitECandidate.Runtime.TransactionU256FieldHeapFrame
import InitECandidate.Runtime.PanSeqAssoc
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_u256_field_returned_heap_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
        (.seq (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))
          (.return (.var .local (ofString "tx"))))) = (some (.returned value),post)) :
    ∀ watched, post.globals.lookup watched = state.globals.lookup watched := by
  intro watched
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
      have kept := transaction_u256_field_normal_heap_frame state middle tx offset arguments
        array index maximum input inputLength scratch frame count ceiling inputLimit args valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove txLocal before fieldRun
      have globals := evaluate_avoidsGlobalAssignment watched
        (.return (.var .local (ofString "tx"))) (by rfl) middle
      dsimp only at run
      rw [run] at globals
      exact globals.trans (kept.2.1 watched)

#print axioms transaction_u256_field_returned_heap_globals
end InitECandidate.Runtime
