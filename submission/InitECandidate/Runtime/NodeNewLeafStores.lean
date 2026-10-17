import InitECandidate.Runtime.FrameHalt
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodeNewLeafStores : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_node_new_leaf with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

theorem source_nodeNewLeaf_stores : nodeNewLeafStores = .seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 1)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 8]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 16]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 32]) (.var .local (ofString "nib"))) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 40]) (.var .local (ofString "nlen"))) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 48]) (.var .local (ofString "vptr"))) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 56]) (.var .local (ofString "vlen"))) ((.return (.var .local (ofString "nd"))))))))))) := by
  simp only [nodeNewLeafStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def nodeNewLeafStoresPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib nlen vptr vlen : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state (pointer + 0) 1) (pointer + 8) 0) (pointer + 16) 0) (pointer + 24) 0) (pointer + 32) nib) (pointer + 40) nlen) (pointer + 48) vptr) (pointer + 56) vlen)

theorem evaluate_nodeNewLeaf_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib nlen vptr vlen : BitVec 64)
    (ndLocal : state.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (nibLocal : state.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (vptrLocal : state.locals.lookup (ofString "vptr") = some (.val (.word vptr)))
    (vlenLocal : state.locals.lookup (ofString "vlen") = some (.val (.word vlen)))
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state nodeNewLeafStores =
      (some (.returned (.val (.word pointer))),nodeNewLeafStoresPost state pointer nib nlen vptr vlen) := by
  let s1 := sourceWriteWord state (pointer + 0) 1
  have step0 : evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 1)) = (none,s1) := by
    apply evaluate_store_word state (pointer + 0) 1
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
  let s6 := sourceWriteWord s5 (pointer + 40) nlen
  have step5 : evaluateHOLFiniteState s5 (.store (.op .add [.var .local (ofString "nd"),.const 40]) (.var .local (ofString "nlen"))) = (none,s6) := by
    apply evaluate_store_word s5 (pointer + 40) nlen
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,nlenLocal,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 40 (by simp)
  let s7 := sourceWriteWord s6 (pointer + 48) vptr
  have step6 : evaluateHOLFiniteState s6 (.store (.op .add [.var .local (ofString "nd"),.const 48]) (.var .local (ofString "vptr"))) = (none,s7) := by
    apply evaluate_store_word s6 (pointer + 48) vptr
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,vptrLocal,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 48 (by simp)
  let s8 := sourceWriteWord s7 (pointer + 56) vlen
  have step7 : evaluateHOLFiniteState s7 (.store (.op .add [.var .local (ofString "nd"),.const 56]) (.var .local (ofString "vlen"))) = (none,s8) := by
    apply evaluate_store_word s7 (pointer + 56) vlen
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s7,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,vlenLocal,s7,s6,s5,s4,s3,s2,s1,sourceWriteWord]
    · exact domain 56 (by simp)
  rw [source_nodeNewLeaf_stores]
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
  rw [evaluateHOLFiniteState_seq_line780,step7]
  dsimp only
  simp [evaluateHOLFiniteState_return,evalHOLExact,ndLocal,shapeOfHOLExact,nodeNewLeafStoresPost,s8,s7,s6,s5,s4,s3,s2,s1,sourceWriteWord]

theorem nodeNewLeafStoresPost_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib nlen vptr vlen : BitVec 64) :
    (nodeNewLeafStoresPost state pointer nib nlen vptr vlen).memory pointer = .word 1 := by
  simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite]

theorem nodeNewLeafStoresPost_before {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib nlen vptr vlen : BitVec 64) (bounded : pointer.toNat + 64 ≤ 33806089496)
    (address : BitVec 64) (before : address.toNat < pointer.toNat) :
    (nodeNewLeafStoresPost state pointer nib nlen vptr vlen).memory address = state.memory address := by
  have separate (offset : Nat) (small : offset < 64) : address ≠ pointer + BitVec.ofNat 64 offset := by
    intro equal
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    have same := congrArg BitVec.toNat equal
    rw [natural] at same
    omega
  have atPointer : address ≠ pointer := by simpa using separate 0 (by decide)
  simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite,atPointer,
    separate 8 (by decide),separate 16 (by decide),separate 24 (by decide),
    separate 32 (by decide),separate 40 (by decide),separate 48 (by decide),separate 56 (by decide)]

#print axioms evaluate_nodeNewLeaf_stores
#print axioms nodeNewLeafStoresPost_kind
#print axioms nodeNewLeafStoresPost_before
end InitECandidate.Runtime
