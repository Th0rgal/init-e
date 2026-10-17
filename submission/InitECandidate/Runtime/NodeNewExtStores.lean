import InitECandidate.Runtime.FrameHalt
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodeNewExtStores : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_node_new_ext with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

theorem source_nodeNewExt_stores : nodeNewExtStores =
    .seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 2)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 8]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 16]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 32]) (.var .local (ofString "nib"))) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 40]) (.var .local (ofString "nlen"))) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 48]) (.var .local (ofString "child"))) (.return (.var .local (ofString "nd"))))))))) := by
  simp only [nodeNewExtStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def nodeNewExtStoresPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib size child : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (state) (pointer + 0) 2) (pointer + 8) 0) (pointer + 16) 0) (pointer + 24) 0) (pointer + 32) nib) (pointer + 40) size) (pointer + 48) child)

/-- Exact original extension-constructor stores and return, at any clock. -/
theorem evaluate_nodeNewExt_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib size child : BitVec 64)
    (ndLocal : state.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (nibLocal : state.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (sizeLocal : state.locals.lookup (ofString "nlen") = some (.val (.word size)))
    (childLocal : state.locals.lookup (ofString "child") = some (.val (.word child)))
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state nodeNewExtStores =
      (some (.returned (.val (.word pointer))),nodeNewExtStoresPost state pointer nib size child) := by
  let s1 := sourceWriteWord state (pointer + 0) 2
  have step0 : evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 2)) = (none,s1) := by
    apply evaluate_store_word state (pointer + 0) 2
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · simp [evalHOLExact]
    · exact domain 0 (by simp)
  let s2 := sourceWriteWord s1 (pointer + 8) 0
  have step1 : evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "nd"),.const 8]) (.const 0)) = (none,s2) := by
    apply evaluate_store_word s1 (pointer + 8) 0
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s1,sourceWriteWord]
    · simp [evalHOLExact]
    · exact domain 8 (by simp)
  let s3 := sourceWriteWord s2 (pointer + 16) 0
  have step2 : evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "nd"),.const 16]) (.const 0)) = (none,s3) := by
    apply evaluate_store_word s2 (pointer + 16) 0
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s2,s1,sourceWriteWord]
    · simp [evalHOLExact]
    · exact domain 16 (by simp)
  let s4 := sourceWriteWord s3 (pointer + 24) 0
  have step3 : evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.const 0)) = (none,s4) := by
    apply evaluate_store_word s3 (pointer + 24) 0
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact]
    · exact domain 24 (by simp)
  let s5 := sourceWriteWord s4 (pointer + 32) nib
  have step4 : evaluateHOLFiniteState s4 (.store (.op .add [.var .local (ofString "nd"),.const 32]) (.var .local (ofString "nib"))) = (none,s5) := by
    apply evaluate_store_word s4 (pointer + 32) nib
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,nibLocal,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 32 (by simp)
  let s6 := sourceWriteWord s5 (pointer + 40) size
  have step5 : evaluateHOLFiniteState s5 (.store (.op .add [.var .local (ofString "nd"),.const 40]) (.var .local (ofString "nlen"))) = (none,s6) := by
    apply evaluate_store_word s5 (pointer + 40) size
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,sizeLocal,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 40 (by simp)
  let s7 := sourceWriteWord s6 (pointer + 48) child
  have step6 : evaluateHOLFiniteState s6 (.store (.op .add [.var .local (ofString "nd"),.const 48]) (.var .local (ofString "child"))) = (none,s7) := by
    apply evaluate_store_word s6 (pointer + 48) child
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,childLocal,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 48 (by simp)
  rw [source_nodeNewExt_stores]
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
  rw [evaluateHOLFiniteState_seq_line780,step6]
  dsimp only
  simp [evaluateHOLFiniteState_return,evalHOLExact,ndLocal,shapeOfHOLExact,nodeNewExtStoresPost,s7,s6,s5,s4,s3,s2,s1,sourceWriteWord]

#print axioms source_nodeNewExt_stores
#print axioms evaluate_nodeNewExt_stores
end InitECandidate.Runtime
