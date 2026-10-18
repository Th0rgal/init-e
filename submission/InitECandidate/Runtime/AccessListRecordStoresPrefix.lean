import InitECandidate.Runtime.AccessListSource
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessRecordStores : ProgHOL 64 :=
  match accessRecordScope with | .dec _ _ _ body => body | _ => .skip

theorem source_access_record_stores : accessRecordStores =
    .seq (.store (.op .add [.var .local (ofString "rec"),.const 0]) (.var .local (ofString "addr")))
    (.seq (.store (.op .add [.var .local (ofString "rec"),.const 8]) (.var .local (ofString "keys")))
    (.seq (.store (.op .add [.var .local (ofString "rec"),.const 16]) (.rfield 1 (.var .local (ofString "slots"))))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := by
  simp only [accessRecordStores,accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Record completion only modifies its three destination words. -/
theorem access_record_stores_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record address keys slots count watched : BitVec 64)
    (atRecord : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (atAddress : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (atKeys : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (atSlots : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word slots),.val (.word count)]))
    (apart0 : watched ≠ record + 0#64) (apart8 : watched ≠ record + 8#64) (apart16 : watched ≠ record + 16#64) :
    (evaluateHOLFiniteState state accessRecordStores).2.memory watched = state.memory watched := by
  have chain : BoundWordStoreChainFrame (F := F) state.locals watched accessRecordStores := by
    rw [source_access_record_stores]
    apply BoundWordStoreChainFrame.store
    · intro current same
      refine ⟨record + 0#64,?_,apart0⟩
      simp [evalHOLExact,evalListHOLExact,same,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro current same parsed evaluated
      have actual : @evalHOLExact 64 F _ current.toExact
          (fun a => Classical.propDecidable (current.memaddrs a)) (.var .local (ofString "addr")) = some (.val (.word address)) := by
        simp [evalHOLExact,same,atAddress]
      rw [actual] at evaluated
      exact ⟨address,(Option.some.inj evaluated).symm⟩
    apply BoundWordStoreChainFrame.store
    · intro current same
      refine ⟨record + 8#64,?_,apart8⟩
      simp [evalHOLExact,evalListHOLExact,same,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro current same parsed evaluated
      have actual : @evalHOLExact 64 F _ current.toExact
          (fun a => Classical.propDecidable (current.memaddrs a)) (.var .local (ofString "keys")) = some (.val (.word keys)) := by
        simp [evalHOLExact,same,atKeys]
      rw [actual] at evaluated
      exact ⟨keys,(Option.some.inj evaluated).symm⟩
    apply BoundWordStoreChainFrame.store
    · intro current same
      refine ⟨record + 16#64,?_,apart16⟩
      simp [evalHOLExact,evalListHOLExact,same,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro current same parsed evaluated
      have actual : @evalHOLExact 64 F _ current.toExact
          (fun a => Classical.propDecidable (current.memaddrs a)) (.rfield 1 (.var .local (ofString "slots"))) = some (.val (.word count)) := by
        simp [evalHOLExact,same,atSlots]
      rw [actual] at evaluated
      exact ⟨count,(Option.some.inj evaluated).symm⟩
    exact BoundWordStoreChainFrame.tail _ (by rfl)
  exact evaluate_boundWordStoreChain_frame chain state rfl

/-- A nonwrapping record after an earlier array preserves that array's input prefix. -/
theorem access_record_stores_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record address keys slots count array outerCount input inputLength : BitVec 64)
    (atRecord : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (atAddress : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (atKeys : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (atSlots : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word slots),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength outerCount.toNat)
    (before : array.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (fits : record.toNat + 24 < 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state accessRecordStores).2 array input inputLength outerCount.toNat := by
  have n0 : (record + 0#64).toNat = record.toNat := by simp
  have n8 : (record + 8#64).toNat = record.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 8 < 2^64; omega)]
    rfl
  have n16 : (record + 16#64).toNat = record.toNat + 16 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 16 < 2^64; omega)]
    rfl
  apply valid.after_memory_below state _ array outerCount input inputLength record before
    (evaluateHOLFiniteState_metadata state accessRecordStores).2.1
  intro watched below
  apply access_record_stores_memory_frame state record address keys slots count watched atRecord atAddress atKeys atSlots
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [n0] at same
    omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [n8] at same
    omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [n16] at same
    omega

#print axioms access_record_stores_memory_frame
#print axioms access_record_stores_input_prefix
end InitECandidate.Runtime
