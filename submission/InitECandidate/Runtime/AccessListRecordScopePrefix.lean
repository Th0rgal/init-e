import InitECandidate.Runtime.AccessListRecordStoresPrefix
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_access_record_scope : accessRecordScope =
    .dec (ofString "rec") .one
      (.op .add [.var .local (ofString "recs"),.panop .mul [.var .local (ofString "i"),.const 24]]) accessRecordStores := by
  simp only [accessRecordScope,accessRecordStores,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Completing the actual record-address scope preserves an earlier input array. -/
theorem access_record_scope_normal_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (records index address keys slots count array outerCount input inputLength : BitVec 64)
    (atRecords : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atAddress : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (atKeys : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (atSlots : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word slots),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength outerCount.toNat)
    (before : array.toNat + outerCount.toNat * 16 ≤ (records + index * 24#64).toNat)
    (fits : (records + index * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessRecordScope = (none,post)) :
    RlpSliceInputPrefix post array input inputLength outerCount.toNat := by
  rw [source_access_record_scope] at run
  obtain ⟨value,output,initialized,bodyRun,restored⟩ := evaluate_dec_normal_scope state post _ _ _ _ run
  have actual : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "recs"),.panop .mul [.var .local (ofString "i"),.const 24]]) =
      some (.val (.word (records + index * 24#64))) := by
    simp [evalHOLExact,evalListHOLExact,atRecords,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  rw [actual] at initialized
  have valueEq := Option.some.inj initialized
  subst value
  let entered := setVarHOLFinite (ofString "rec") (.val (.word (records + index * 24#64))) state
  have retained := access_record_stores_input_prefix entered (records + index * 24#64) address keys slots count
    array outerCount input inputLength
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "rec" ≠ ofString "addr" by decide] using atAddress)
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "rec" ≠ ofString "keys" by decide] using atKeys)
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "rec" ≠ ofString "slots" by decide] using atSlots)
    (by
      intro slot inside
      obtain ⟨pointer,length,entry⟩ := valid slot inside
      exact ⟨pointer,length,entry.after_frame state entered array slot pointer length input inputLength rfl rfl rfl⟩) before fits
  change evaluateHOLFiniteState entered accessRecordStores = (none,output) at bodyRun
  rw [bodyRun] at retained
  subst post
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := retained slot inside
  exact ⟨pointer,length,entry.after_frame output _ array slot pointer length input inputLength rfl rfl rfl⟩

#print axioms access_record_scope_normal_input_prefix
end InitECandidate.Runtime
