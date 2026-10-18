import InitECandidate.Runtime.AuthorizationsWordAssignmentBound
import InitECandidate.Runtime.AuthorizationsWord2Source
import InitECandidate.Runtime.AuthorizationsRScalarBound
import InitECandidate.Runtime.AuthorizationsWordTailSource
import InitECandidate.Runtime.WordStoreInputPrefix
import InitECandidate.Runtime.AuthorizationsRTailSource
import InitECandidate.Runtime.FourWordStoreInputPrefix
import InitECandidate.Runtime.AuthorizationsLastScalarBound
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarU256DeclarationInputBound
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual word store at record offset40 adds no source clocks to the
checked final three scalar extractions and preserves the input-prefix premise. -/
theorem evaluate_authorization_word2_store_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record word array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (atValue : state.locals.lookup (ofString "w") =
      some (.val (.word word)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state authorizationWord2Store
    state.clock ≤ evaluated.2.clock + 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let destination : ExpHOL 64 := .op .add [.var .local (ofString "a"),.const 40]
  let value : ExpHOL 64 := .var .local (ofString "w")
  let store : ProgHOL 64 := .store destination value
  have addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word (record + 40#64))) := by
    simp [destination,evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
  have valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
      some (.val (.word word)) := by
    simp [value,evalHOLExact,atValue]
  have addressNat : (record + 40#64).toNat = record.toNat + 40 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 40 < 2^64; omega)]
    rfl
  have retained := wordStore_input_prefix state destination value (record + 40#64) word
    array count input inputLength addressEval valueEval valid (by rw [addressNat]; omega)
  have control := evaluate_store_control_frame state destination value
  have metadata := evaluateHOLFiniteState_metadata state store
  have scratchSame := evaluate_avoidsGlobalAssignment (ofString "scratch_ptr") store (by rfl) state
  have frameSame := evaluate_avoidsGlobalAssignment (ofString "frame_mem_ptr") store (by rfl) state
  rw [source_authorization_word2_store,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state store with
  | mk result post =>
    rw [run] at metadata scratchSame frameSame
    change RlpSliceInputPrefix (evaluateHOLFiniteState state store).2 array input inputLength count.toNat at retained
    change ((evaluateHOLFiniteState state store).1 = none ∨ (evaluateHOLFiniteState state store).1 = some .error) ∧
      (evaluateHOLFiniteState state store).2.locals = state.locals ∧
      (evaluateHOLFiniteState state store).2.clock = state.clock at control
    rw [run] at retained control
    dsimp only at metadata scratchSame frameSame control retained
    cases result with
    | none =>
      have entered : post.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
        rw [control.2.1]; exact entryLocal
      have postRecord : post.locals.lookup (ofString "a") = some (.val (.word record)) := by
        rw [control.2.1]; exact atRecord
      have bounded := evaluate_authorization_word_assignment_bounded post record array count input inputLength scratch frame
        ceiling inputLimit postRecord before fits entered retained inside inputBound limitBound (scratchSame.trans scratchGlobal)
        (frameSame.trans frameGlobal) (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by simpa only [metadata.2.1] using arena) arrayBelowFrame (by omega)
      dsimp only
      exact ⟨by dsimp only at bounded; omega,by dsimp only at bounded; omega,bounded.2.2⟩
    | some result =>
      have error : result = .error := by simpa using control.1
      subst result
      dsimp only
      exact ⟨by omega,by omega,by simp⟩

#print axioms evaluate_authorization_word2_store_bounded
end InitECandidate.Runtime
