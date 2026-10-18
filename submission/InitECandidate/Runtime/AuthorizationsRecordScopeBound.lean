import InitECandidate.Runtime.AuthorizationsRecordSource
import InitECandidate.Runtime.AuthorizationsCidDeclarationBound
import InitECandidate.Runtime.AuthorizationsCidStoreBound
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.TxScalarU256InputPrefix
import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.AuthorizationsRStoreLastBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
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
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Computing and scoping the actual record address adds no source clocks
to all six field extractions, stores and the outer index increment. -/
theorem evaluate_authorization_record_scope_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record records index array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
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
    (budget : 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state authorizationRecordScope
    state.clock ≤ evaluated.2.clock + 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let initial := setVarHOLFinite (ofString "a") (.val (.word record)) state
  have atRecord : initial.locals.lookup (ofString "a") = some (.val (.word record)) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atEntry : initial.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "a" ≠ ofString "ent" by decide] using entryLocal
  have initialPrefix : RlpSliceInputPrefix initial array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state initial array slot p n input inputLength rfl rfl rfl⟩
  have bound := evaluate_authorization_cid_declaration_bounded initial record array count input inputLength scratch frame
    ceiling inputLimit atRecord before fits atEntry initialPrefix inside inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena arrayBelowFrame budget
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "recs"),.panop .mul [.var .local (ofString "i"),.const 120]]) =
      some (.val (.word record)) := by
    simp [evalHOLExact,evalListHOLExact,recordsLocal,indexLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,recordAddress]
  rw [source_authorization_record_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initializer]
  simp only [shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState initial authorizationCidDeclaration with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_authorization_record_scope_bounded
end InitECandidate.Runtime
