import InitECandidate.Runtime.AuthorizationsLastScalarGlobalFrame
import InitECandidate.Runtime.AuthorizationsLastScalarOuterPrefix
import InitECandidate.Runtime.FourWordStoreBeforeInputPrefix
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

/-- Successful r-limb storage and final scalar extraction preserve all globals. -/
theorem authorization_r_store_and_last_normal_global_frame {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record first second third fourth array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (atValue : state.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (runFinal : evaluateHOLFiniteState state authorizationRStoreAndLast = (none,final)) :
    ∀ watched : MlS, final.globals.lookup watched = state.globals.lookup watched := by
  let destination : ExpHOL 64 := .op .add [.var .local (ofString "a"),.const 56]
  let value : ExpHOL 64 := .var .local (ofString "r")
  let store : ProgHOL 64 := .store destination value
  have addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word (record + 56#64))) := by
    simp [destination,evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
  have valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    simp [value,evalHOLExact,atValue]
  have addressNat : (record + 56#64).toNat = record.toNat + 56 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 56 < 2^64; omega)]
    rfl
  have retained : RlpSliceInputPrefix (evaluateHOLFiniteState state store).2 array input inputLength count.toNat := by
    rcases before with arrayBefore | recordBefore
    · exact fourWordStore_input_prefix state destination value (record + 56#64) first second third fourth array count input inputLength addressEval valueEval valid (by rw [addressNat]; omega) (by rw [addressNat]; omega)
    · exact fourWordStore_before_input_prefix state destination value (record + 56#64) first second third fourth array count input inputLength addressEval valueEval valid (by have limit := frame.isLt; omega) (by rw [addressNat]; omega)
  have control := evaluate_store_control_frame state destination value
  have metadata := evaluateHOLFiniteState_metadata state store
  have scratchSame := evaluate_avoidsGlobalAssignment (ofString "scratch_ptr") store (by rfl) state
  have frameSame := evaluate_avoidsGlobalAssignment (ofString "frame_mem_ptr") store (by rfl) state
  rw [source_authorization_r_store_and_last,evaluateHOLFiniteState_seq_line780] at runFinal
  cases run : evaluateHOLFiniteState state store with
  | mk result post =>
    rw [run] at metadata scratchSame frameSame runFinal
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
      have atRecordPost : post.locals.lookup (ofString "a") = some (.val (.word record)) := by
        rw [control.2.1]; exact atRecord
      have kept := authorization_last_scalar_normal_global_frame post final array count input inputLength scratch frame
        ceiling inputLimit entered retained inside inputBound limitBound
        (scratchSame.trans scratchGlobal) (frameSame.trans frameGlobal) (metadata.1.trans code)
        orderedFrame framePositive scratchBelow (by simpa only [metadata.2.1] using arena) (by omega) runFinal
      intro watched
      have same := evaluate_avoidsGlobalAssignment watched store (by rfl) state
      rw [run] at same
      exact (kept watched).trans same
    | some result =>
      have error : result = .error := by simpa using control.1
      subst result
      cases runFinal

#print axioms authorization_r_store_and_last_normal_global_frame
end InitECandidate.Runtime
