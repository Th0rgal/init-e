import InitECandidate.Runtime.PayloadStoreTailMemoryFrame
import InitECandidate.Runtime.StatelessHashRequestWitnessReturned
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The remaining scalar field stores cannot overwrite the slice metadata. -/
theorem payload_scalar_tail_memory_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F) (payload watched : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (separate : ∀ offset : BitVec 64, offset ∈ ([80,88,96,104,112,120,128] : List (BitVec 64)) →
      watched ≠ payload + offset) :
    (evaluateHOLFiniteState state (payloadAt 24)).2.memory watched = state.memory watched := by
  apply evaluate_boundWordStoreChain_frame (bindings := state.locals) ?_ state rfl
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  change BoundWordStoreChainFrame state.locals watched (.seq (.store _ _) _)
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 80, ?_, separate 80 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 88, ?_, separate 88 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 96, ?_, separate 96 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 104, ?_, separate 104 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 112, ?_, separate 112 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 120, ?_, separate 120 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 128, ?_, separate 128 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  exact BoundWordStoreChainFrame.tail _ rfl


/-- Every successful return of the actual final decoder stores exports the
withdrawal and request slice entries consumed by the hash. Readability follows
from the successful stores themselves. -/
theorem payload_store_tail_returned_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload input length wd balance count : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atWd : state.locals.lookup (ofString "o_wd") = some (.val (.word wd)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (atCount : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (run : evaluateHOLFiniteState state (payloadAt 20) = (some (.returned value),post)) :
    RlpSliceEntry post payload 3 (input + wd) count ∧
      RlpSliceEntry post payload 4 (input + balance) (length - balance) := by
  have source0 : payloadAt 20 = .seq (.store (.op .add [.var .local (ofString "pl"),.const 48]) (.op .add [.var .local (ofString "p"),.var .local (ofString "o_wd")])) (payloadAt 21) := by
    simp only [payloadAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source0] at run
  obtain ⟨d48,r1⟩ := seqStore_returned_exact state post _ _ _ (payload + 48) (input + wd) value
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,evalListHOLExact,atInput,atLength,atWd,atBalance,atCount,wordOpHOL,wordOp,valueIsWord,valueWord]) run
  let s1 : PanSemStateFiniteExact 64 F := {state with memory := wmem state.memory (payload + 48) (input + wd)}
  change evaluateHOLFiniteState s1 (payloadAt 21) = _ at r1
  have source1 : payloadAt 21 = .seq (.store (.op .add [.var .local (ofString "pl"),.const 56]) (.var .local (ofString "nwd"))) (payloadAt 22) := by
    simp only [payloadAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source1] at r1
  obtain ⟨d56,r2⟩ := seqStore_returned_exact s1 post _ _ _ (payload + 56) (count) value
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,s1])
    (by simp [evalHOLExact,evalListHOLExact,atInput,atLength,atWd,atBalance,atCount,wordOpHOL,wordOp,valueIsWord,valueWord,s1]) r1
  let s2 : PanSemStateFiniteExact 64 F := {s1 with memory := wmem s1.memory (payload + 56) (count)}
  change evaluateHOLFiniteState s2 (payloadAt 22) = _ at r2
  have source2 : payloadAt 22 = .seq (.store (.op .add [.var .local (ofString "pl"),.const 64]) (.op .add [.var .local (ofString "p"),.var .local (ofString "o_bal")])) (payloadAt 23) := by
    simp only [payloadAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source2] at r2
  obtain ⟨d64,r3⟩ := seqStore_returned_exact s2 post _ _ _ (payload + 64) (input + balance) value
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,s2,s1])
    (by simp [evalHOLExact,evalListHOLExact,atInput,atLength,atWd,atBalance,atCount,wordOpHOL,wordOp,valueIsWord,valueWord,s2,s1]) r2
  let s3 : PanSemStateFiniteExact 64 F := {s2 with memory := wmem s2.memory (payload + 64) (input + balance)}
  change evaluateHOLFiniteState s3 (payloadAt 23) = _ at r3
  have source3 : payloadAt 23 = .seq (.store (.op .add [.var .local (ofString "pl"),.const 72]) (.op .sub [.var .local (ofString "len"),.var .local (ofString "o_bal")])) (payloadAt 24) := by
    simp only [payloadAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source3] at r3
  obtain ⟨d72,r4⟩ := seqStore_returned_exact s3 post _ _ _ (payload + 72) (length - balance) value
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,s3,s2,s1])
    (by simp [evalHOLExact,evalListHOLExact,atInput,atLength,atWd,atBalance,atCount,wordOpHOL,wordOp,valueIsWord,valueWord,s3,s2,s1]) r3
  let s4 : PanSemStateFiniteExact 64 F := {s3 with memory := wmem s3.memory (payload + 72) (length - balance)}
  change evaluateHOLFiniteState s4 (payloadAt 24) = _ at r4
  have domain := evaluateHOLFiniteState_metadata s4 (payloadAt 24)
  rw [r4] at domain
  have frame (off : BitVec 64) (member : off ∈ ([48,56,64,72] : List (BitVec 64))) : post.memory (payload + off) = s4.memory (payload + off) := by
    have kept := payload_scalar_tail_memory_frame s4 payload (payload + off) atPayload (by
      intro later hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member hl
      rcases member with rfl | rfl | rfl | rfl
      all_goals rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp)
    rw [r4] at kept
    exact kept
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [s4,s3,s2,s1] using (domain.2.1 ▸ d48)
    · simpa [s4,s3,s2,s1,BitVec.add_assoc] using (domain.2.1 ▸ d56)
    · change post.memory (payload + 48) = _
      rw [frame 48 (by simp)]
      simp [s4,s3,s2,s1,wmem]
    · change post.memory (payload + 48 + 8) = _
      rw [show payload + 48 + 8 = payload + 56 by simp [BitVec.add_assoc],frame 56 (by simp)]
      simp [s4,s3,s2,s1,wmem]
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [s4,s3,s2,s1] using (domain.2.1 ▸ d64)
    · simpa [s4,s3,s2,s1,BitVec.add_assoc] using (domain.2.1 ▸ d72)
    · change post.memory (payload + 64) = _
      rw [frame 64 (by simp)]
      simp [s4,s3,s2,s1,wmem]
    · change post.memory (payload + 64 + 8) = _
      rw [show payload + 64 + 8 = payload + 72 by simp [BitVec.add_assoc],frame 72 (by simp)]
      simp [s4,s3,s2,s1,wmem]

#print axioms payload_scalar_tail_memory_frame
#print axioms payload_store_tail_returned_entries
end InitECandidate.Runtime
