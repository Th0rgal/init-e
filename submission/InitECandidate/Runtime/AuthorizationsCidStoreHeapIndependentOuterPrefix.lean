import InitECandidate.Runtime.AuthorizationsCidStoreIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsCidSource
import InitECandidate.Runtime.AuthorizationsAddressDeclarationHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLastScalarHeapIndependentOuterPrefix
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
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful chain-id storage and all later fields preserve the outer slice array. -/
theorem authorization_cid_store_normal_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record first second third fourth array count input inputLength scratch frame outerArray outerCount outerInput outerLength : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (atValue : state.locals.lookup (ofString "cid") =
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
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (budget : 5 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (runFinal : evaluateHOLFiniteState state authorizationCidStore = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let destination : ExpHOL 64 := .op .add [.var .local (ofString "a"),.const 0]
  let value : ExpHOL 64 := .var .local (ofString "cid")
  let store : ProgHOL 64 := .store destination value
  have addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word (record + 0#64))) := by
    simp [destination,evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
  have valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    simp [value,evalHOLExact,atValue]
  have addressNat : (record + 0#64).toNat = record.toNat + 0 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 0 < 2^64; omega)]
    rfl
  have retained : RlpSliceInputPrefix (evaluateHOLFiniteState state store).2 array input inputLength count.toNat := by
    rcases before with arrayBefore | recordBefore
    · exact fourWordStore_input_prefix state destination value (record + 0#64) first second third fourth array count input inputLength addressEval valueEval valid (by rw [addressNat]; omega) (by rw [addressNat]; omega)
    · exact fourWordStore_before_input_prefix state destination value (record + 0#64) first second third fourth array count input inputLength addressEval valueEval valid (by have limit := frame.isLt; omega) (by rw [addressNat]; omega)
  have outerRetained := fourWordStore_input_prefix state destination value (record + 0#64)
    first second third fourth outerArray outerCount outerInput outerLength addressEval valueEval outerValid
    (by rw [addressNat]; omega) (by rw [addressNat]; omega)
  have control := evaluate_store_control_frame state destination value
  have metadata := evaluateHOLFiniteState_metadata state store
  have scratchSame := evaluate_avoidsGlobalAssignment (ofString "scratch_ptr") store (by rfl) state
  have frameSame := evaluate_avoidsGlobalAssignment (ofString "frame_mem_ptr") store (by rfl) state
  rw [source_authorization_cid_store,evaluateHOLFiniteState_seq_line780] at runFinal
  cases run : evaluateHOLFiniteState state store with
  | mk result post =>
    rw [run] at metadata scratchSame frameSame outerRetained runFinal
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
      exact authorization_address_declaration_normal_heap_independent_outer_prefix post final record array count input inputLength scratch frame
        outerArray outerCount outerInput outerLength ceiling inputLimit atRecordPost entered retained inside inputBound limitBound
        (scratchSame.trans scratchGlobal) (frameSame.trans frameGlobal) (metadata.1.trans code)
        orderedFrame framePositive scratchBelow (by simpa only [metadata.2.1] using arena)
        arrayFits arrayAbove before (by omega) outerRetained outerFits outerAbove outerBeforeRecord fits runFinal
    | some result =>
      have error : result = .error := by simpa using control.1
      subst result
      cases runFinal

#print axioms authorization_cid_store_normal_heap_independent_outer_prefix
end InitECandidate.Runtime
