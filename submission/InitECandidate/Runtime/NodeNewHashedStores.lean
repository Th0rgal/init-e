import InitECandidate.Runtime.FrameHalt
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodeNewHashedStores : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_node_new_hashed with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

theorem source_nodeNewHashed_stores : nodeNewHashedStores = .seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 8]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 16]) (.const 0)) (.seq (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "hash"))) ((.return (.var .local (ofString "nd"))))))) := by
  simp only [nodeNewHashedStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def nodeNewHashedStoresPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state pointer 0)
    (pointer + 8) 0) (pointer + 16) 0) (pointer + 24) hash)

theorem evaluate_nodeNewHashed_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash : BitVec 64)
    (ndLocal : state.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state nodeNewHashedStores =
      (some (.returned (.val (.word pointer))),nodeNewHashedStoresPost state pointer hash) := by
  let s1 := sourceWriteWord state pointer 0
  have step0 : evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 0)) = (none,s1) := by
    apply evaluate_store_word state pointer 0
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · simp [evalHOLExact]
    · simpa using domain 0 (by simp)
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
  let s4 := sourceWriteWord s3 (pointer + 24) hash
  have step3 : evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "hash"))) = (none,s4) := by
    apply evaluate_store_word s3 (pointer + 24) hash
    · simp [evalHOLExact,evalListHOLExact,ndLocal,wordOpHOL,wordOp,valueIsWord,valueWord,s3,s2,s1,sourceWriteWord]
    · simp [evalHOLExact,hashLocal,s3,s2,s1,sourceWriteWord]
    · exact domain 24 (by simp)
  rw [source_nodeNewHashed_stores]
  rw [evaluateHOLFiniteState_seq_line780,step0]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step1]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,step3]
  dsimp only
  simp [evaluateHOLFiniteState_return,evalHOLExact,ndLocal,shapeOfHOLExact,nodeNewHashedStoresPost,s4,s3,s2,s1,sourceWriteWord]

theorem nodeNewHashedStoresPost_kind {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer hash : BitVec 64) :
    (nodeNewHashedStoresPost state pointer hash).memory pointer = .word 0 := by
  simp [nodeNewHashedStoresPost,sourceWriteWord,emptyLocalsHOLFinite]

theorem nodeNewHashedStoresPost_before {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash : BitVec 64) (bounded : pointer.toNat + 32 ≤ 33806089496)
    (address : BitVec 64) (before : address.toNat < pointer.toNat) :
    (nodeNewHashedStoresPost state pointer hash).memory address = state.memory address := by
  have separate (offset : Nat) (small : offset < 32) : address ≠ pointer + BitVec.ofNat 64 offset := by
    intro equal
    have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    have same := congrArg BitVec.toNat equal
    rw [natural] at same
    omega
  have atPointer : address ≠ pointer := by simpa using separate 0 (by decide)
  simp [nodeNewHashedStoresPost,sourceWriteWord,emptyLocalsHOLFinite,atPointer,
    separate 8 (by decide),separate 16 (by decide),separate 24 (by decide)]

#print axioms evaluate_nodeNewHashed_stores
#print axioms nodeNewHashedStoresPost_kind
#print axioms nodeNewHashedStoresPost_before
end InitECandidate.Runtime
