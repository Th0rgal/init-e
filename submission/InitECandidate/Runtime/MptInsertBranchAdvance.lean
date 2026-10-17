import InitECandidate.Runtime.MptInsertCommit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertBranchAdvance : ProgHOL 64 :=
  match mptInsertKindDispatch with
  | .seq _ (.seq _ (.ite _ _ (.ite _ _ (.ite _ _ (.dec _ _ _ body))))) => body
  | _ => .skip

def mptInsertBranchChildAddress : ExpHOL 64 :=
  .op .add [.var .local (ofString "node"),.const 32,
    .panop .mul [.var .local (ofString "idx"),.const 8]]

theorem source_mptInsert_branch_advance : mptInsertBranchAdvance =
    .seq (.assign .local (ofString "r") (.var .local (ofString "node")))
      (.seq (.assign .local (ofString "next_node") (.load .one mptInsertBranchChildAddress))
        (.seq (.assign .local (ofString "next_slot") mptInsertBranchChildAddress)
          (.seq (.assign .local (ofString "next_level")
            (.op .add [.var .local (ofString "level"),.const 1]))
            (.assign .local (ofString "go") (.const 1))))) := by
  simp only [mptInsertBranchAdvance,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original branch path prepares a live/null child, a typed branch
backlink, and a key level advanced by exactly one. -/
theorem evaluate_mptInsert_branch_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (registry : TrieWalkRegistry live extensions branches state)
    (node level child keyLength : BitVec 64) (slot : Nat) (slotSmall : slot < 16) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (indexLocal : state.locals.lookup (ofString "idx") = some (.val (.word (BitVec.ofNat 64 slot))))
    (childField : state.memory (branchChildAddress node slot) = .word child)
    (domain : state.memaddrs (branchChildAddress node slot))
    (fits : level.toNat < keyLength.toNat)
    (oldResult : BitVec 64) (oldResultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (oldNode : BitVec 64) (oldNodeLocal : state.locals.lookup (ofString "next_node") = some (.val (.word oldNode)))
    (oldSlot : BitVec 64) (oldSlotLocal : state.locals.lookup (ofString "next_slot") = some (.val (.word oldSlot)))
    (oldLevel : BitVec 64) (oldLevelLocal : state.locals.lookup (ofString "next_level") = some (.val (.word oldLevel)))
    (oldGo : BitVec 64) (oldGoLocal : state.locals.lookup (ofString "go") = some (.val (.word oldGo)))
    : ∃ post, evaluateHOLFiniteState state mptInsertBranchAdvance = (none,post) ∧
      post.locals.lookup (ofString "r") = some (.val (.word node)) ∧
      post.locals.lookup (ofString "next_node") = some (.val (.word child)) ∧ (child = 0 ∨ child ∈ live) ∧
      post.locals.lookup (ofString "next_slot") = some (.val (.word (branchChildAddress node slot))) ∧
      TrieChildSlot post extensions branches (branchChildAddress node slot) ∧
      post.locals.lookup (ofString "next_level") = some (.val (.word (level + 1))) ∧
      level.toNat < (level + 1).toNat ∧ (level + 1).toNat ≤ keyLength.toNat ∧
      post.locals.lookup (ofString "go") = some (.val (.word (1 : BitVec 64))) ∧
      post.memory = state.memory ∧ post.clock = state.clock := by
  simp [ofString] at nodeLocal levelLocal indexLocal
  let s1 := setVarHOLFinite (ofString "r") (.val (.word node)) state
  have old0 : state.locals.lookup (ofString "r") = some (.val (.word oldResult)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldResultLocal
  have value0 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "node")) = some (.val (.word node)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertBranchChildAddress,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField,BitVec.add_assoc]
  have step0 := evaluate_local_word_assignment state (ofString "r") (.var .local (ofString "node")) oldResult node old0 value0
  let s2 := setVarHOLFinite (ofString "next_node") (.val (.word child)) s1
  have old1 : s1.locals.lookup (ofString "next_node") = some (.val (.word oldNode)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldNodeLocal
  have value1 : @evalHOLExact 64 F _ s1.toExact
      (fun address => Classical.propDecidable (s1.memaddrs address)) (.load .one mptInsertBranchChildAddress) = some (.val (.word child)) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertBranchChildAddress,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField,BitVec.add_assoc]
    change @memLoadHOLExact 64 _ .one (node + (32 + BitVec.ofNat 64 slot * 8)) state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.memory state.structs = _
    simp [memLoadHOLExact,domain,childField,BitVec.add_assoc]
    have addressEq : branchChildAddress node slot = node + (BitVec.ofNat 64 32 + BitVec.ofNat 64 slot * BitVec.ofNat 64 8) := by
      simp [branchChildAddress,BitVec.add_assoc]
    rw [addressEq] at domain childField
    exact ⟨domain,childField⟩
  have step1 := evaluate_local_word_assignment s1 (ofString "next_node") (.load .one mptInsertBranchChildAddress) oldNode child old1 value1
  let s3 := setVarHOLFinite (ofString "next_slot") (.val (.word (branchChildAddress node slot))) s2
  have old2 : s2.locals.lookup (ofString "next_slot") = some (.val (.word oldSlot)) := by
    simpa [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldSlotLocal
  have value2 : @evalHOLExact 64 F _ s2.toExact
      (fun address => Classical.propDecidable (s2.memaddrs address)) mptInsertBranchChildAddress = some (.val (.word (branchChildAddress node slot))) := by
    simp [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertBranchChildAddress,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField,BitVec.add_assoc]
  have step2 := evaluate_local_word_assignment s2 (ofString "next_slot") mptInsertBranchChildAddress oldSlot (branchChildAddress node slot) old2 value2
  let s4 := setVarHOLFinite (ofString "next_level") (.val (.word (level + 1))) s3
  have old3 : s3.locals.lookup (ofString "next_level") = some (.val (.word oldLevel)) := by
    simpa [s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldLevelLocal
  have value3 : @evalHOLExact 64 F _ s3.toExact
      (fun address => Classical.propDecidable (s3.memaddrs address)) (.op .add [.var .local (ofString "level"),.const 1]) = some (.val (.word (level + 1))) := by
    simp [s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertBranchChildAddress,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField,BitVec.add_assoc]
  have step3 := evaluate_local_word_assignment s3 (ofString "next_level") (.op .add [.var .local (ofString "level"),.const 1]) oldLevel (level + 1) old3 value3
  let s5 := setVarHOLFinite (ofString "go") (.val (.word 1)) s4
  have old4 : s4.locals.lookup (ofString "go") = some (.val (.word oldGo)) := by
    simpa [s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldGoLocal
  have value4 : @evalHOLExact 64 F _ s4.toExact
      (fun address => Classical.propDecidable (s4.memaddrs address)) (.const 1) = some (.val (.word 1)) := by
    simp [s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertBranchChildAddress,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField,BitVec.add_assoc]
  have step4 := evaluate_local_word_assignment s4 (ofString "go") (.const 1) oldGo 1 old4 value4
  have addition : (level + 1).toNat = level.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have bound := keyLength.isLt; change level.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨s5,?_,?_,?_,registry.branchChildren node registered slot slotSmall child childField,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · rw [source_mptInsert_branch_advance]
    exact evaluate_seq_none step0 (evaluate_seq_none step1 (evaluate_seq_none step2 (evaluate_seq_none step3 step4)))
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · exact Or.inl ⟨node,registered,slot,slotSmall,rfl⟩
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · rw [addition]; omega
  · rw [addition]; omega
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]

#print axioms source_mptInsert_branch_advance
#print axioms evaluate_mptInsert_branch_advance
end InitECandidate.Runtime
