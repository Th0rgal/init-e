import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.AuthorizationsCidDeclarationOuterPrefix
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

/-- Record address scoping and all six fields preserve the outer slice array. -/
theorem authorization_record_scope_normal_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (record records index array count input inputLength scratch frame outerArray outerCount : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
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
    (budget : 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray input inputLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationRecordScope = (none,post)) :
    RlpSliceInputPrefix post outerArray input inputLength outerCount.toNat := by
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
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "recs"),.panop .mul [.var .local (ofString "i"),.const 120]]) =
      some (.val (.word record)) := by
    simp [evalHOLExact,evalListHOLExact,recordsLocal,indexLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,recordAddress]
  rw [source_authorization_record_scope] at run
  obtain ⟨value,output,initialized,bodyRun,restored⟩ := evaluate_dec_normal_scope state post (ofString "a") .one _ authorizationCidDeclaration run
  rw [initializer] at initialized
  have equal := Option.some.inj initialized
  subst value
  have initialOuter : RlpSliceInputPrefix initial outerArray input inputLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state initial outerArray slot p n input inputLength rfl rfl rfl⟩
  have retained := authorization_cid_declaration_normal_outer_prefix initial output record array count input inputLength scratch frame
    outerArray outerCount ceiling inputLimit atRecord atEntry initialPrefix inside inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena arrayBelowFrame before budget initialOuter outerBelow outerBeforeRecord fits bodyRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n input inputLength rfl rfl rfl⟩

#print axioms authorization_record_scope_normal_outer_prefix
end InitECandidate.Runtime
