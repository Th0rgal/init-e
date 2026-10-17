import InitECandidate.Runtime.DecodeStepExtensionCheck
import InitECandidate.Runtime.TrieNibbleWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepExtensionStores : ProgHOL 64 :=
  match decodeStepExtensionRecord with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_decodeStep_extension_stores : decodeStepExtensionStores =
    (.seq (.store (.op .add [.var .local (ofString "rec"),.const 8]) (.const 1)) (.seq (.store (.op .add [.var .local (ofString "rec"),.const 24]) (.var .local (ofString "arr"))) (.seq (.store (.op .add [.var .local (ofString "rec"),.const 48]) (.var .local (ofString "p"))) (.seq (.store (.op .add [.var .local (ofString "rec"),.const 56]) (.var .local (ofString "n"))) (.seq (.store (.op .add [.var .local (ofString "rec"),.const 64]) (.rfield 0 (.var .local (ofString "cn")))) (.seq (.store (.op .add [.var .local (ofString "rec"),.const 72]) (.rfield 1 (.var .local (ofString "cn")))) (.return (.rstruct [.const 1,.var .local (ofString "rec")])))))))) := by
  simp only [decodeStepExtensionStores,decodeStepExtensionRecord,decodeStepExtensionSuffix,
    decodeStepCompactContinuation,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def decodeStepExtensionStoresPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record arr pointer length nibs count : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state (record + 8) 1) (record + 24) arr) (record + 48) pointer) (record + 56) length) (record + 64) nibs) (record + 72) count)

/-- Exact scratch-record writes in the original parser, including the path
pointer/length fields and its structured continuation-record return. -/
theorem evaluate_decodeStep_extension_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record arr pointer length nibs count leaf : BitVec 64)
    (recordLocal : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (arrLocal : state.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (domain : ∀ offset ∈ ([8,24,48,56,64,72] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state decodeStepExtensionStores =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),
        decodeStepExtensionStoresPost state record arr pointer length nibs count) := by
  let s1 := sourceWriteWord state (record + 8) 1
  have step0 : evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "rec"),.const 8]) (.const 1)) = (none,s1) := by
    apply evaluate_store_word state (record + 8) 1
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · simp [evalHOLExact]
    · exact domain 8 (by simp)
  let s2 := sourceWriteWord s1 (record + 24) arr
  have step1 : evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "rec"),.const 24]) (.var .local (ofString "arr"))) = (none,s2) := by
    apply evaluate_store_word s1 (record + 24) arr
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s1,sourceWriteWord]
    · simp [evalHOLExact,arrLocal,s1,sourceWriteWord]
    · exact domain 24 (by simp)
  let s3 := sourceWriteWord s2 (record + 48) pointer
  have step2 : evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "rec"),.const 48]) (.var .local (ofString "p"))) = (none,s3) := by
    apply evaluate_store_word s2 (record + 48) pointer
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,pointerLocal,s2,s1,sourceWriteWord]
    · exact domain 48 (by simp)
  let s4 := sourceWriteWord s3 (record + 56) length
  have step3 : evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "rec"),.const 56]) (.var .local (ofString "n"))) = (none,s4) := by
    apply evaluate_store_word s3 (record + 56) length
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,lengthLocal,s3,s2,s1,sourceWriteWord]
    · exact domain 56 (by simp)
  let s5 := sourceWriteWord s4 (record + 64) nibs
  have step4 : evaluateHOLFiniteState s4 (.store (.op .add [.var .local (ofString "rec"),.const 64]) (.rfield 0 (.var .local (ofString "cn")))) = (none,s5) := by
    apply evaluate_store_word s4 (record + 64) nibs
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,pathLocal,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 64 (by simp)
  let s6 := sourceWriteWord s5 (record + 72) count
  have step5 : evaluateHOLFiniteState s5 (.store (.op .add [.var .local (ofString "rec"),.const 72]) (.rfield 1 (.var .local (ofString "cn")))) = (none,s6) := by
    apply evaluate_store_word s5 (record + 72) count
    · simp [evalHOLExact,evalListHOLExact,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,pathLocal,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 72 (by simp)
  rw [source_decodeStep_extension_stores]
  rw [evaluateHOLFiniteState_seq_line780,step0]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step1]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step3]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step4]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step5]
  dsimp only
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,recordLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL,decodeStepExtensionStoresPost,s6,s5,s4,s3,s2,s1,sourceWriteWord]

set_option maxHeartbeats 1000000 in
/-- The exact record stores retain the decoded path when scratch fields are
outside its containing words, and expose the fields used by later traversal. -/
theorem decodeStepExtensionStoresPost_path {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record arr pointer length nibs count : BitVec 64)
    (valid : TrieNibbleRange state nibs count)
    (outside : ∀ offset : Nat, offset < count.toNat → ∀ field ∈ ([8,24,48,56,64,72] : List Nat),
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ record + BitVec.ofNat 64 field) :
    let post := decodeStepExtensionStoresPost state record arr pointer length nibs count
    TrieNibbleRange post nibs count ∧ post.memory (record + 64) = .word nibs ∧
      post.memory (record + 72) = .word count ∧ post.clock = state.clock := by
  have v0 := valid
  have v1 := v0.after_word_outside (record + 8) 1 (by
    intro offset inside
    exact outside offset inside 8 (by simp))
  have v2 := v1.after_word_outside (record + 24) arr (by
    intro offset inside
    exact outside offset inside 24 (by simp))
  have v3 := v2.after_word_outside (record + 48) pointer (by
    intro offset inside
    exact outside offset inside 48 (by simp))
  have v4 := v3.after_word_outside (record + 56) length (by
    intro offset inside
    exact outside offset inside 56 (by simp))
  have v5 := v4.after_word_outside (record + 64) nibs (by
    intro offset inside
    exact outside offset inside 64 (by simp))
  have v6 := v5.after_word_outside (record + 72) count (by
    intro offset inside
    exact outside offset inside 72 (by simp))
  refine ⟨v6.after_frame rfl rfl rfl,?_,?_,rfl⟩
  · simp [decodeStepExtensionStoresPost,emptyLocalsHOLFinite,sourceWriteWord]
  · simp [decodeStepExtensionStoresPost,emptyLocalsHOLFinite,sourceWriteWord]

#print axioms decodeStepExtensionStoresPost_path
#print axioms evaluate_decodeStep_extension_stores
end InitECandidate.Runtime
