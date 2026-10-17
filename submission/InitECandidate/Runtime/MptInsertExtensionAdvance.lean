import InitECandidate.Runtime.MptInsertCommit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertExtensionAdvance : ProgHOL 64 :=
  match mptInsertKindDispatch with
  | .seq _ (.seq _ (.ite _ _ (.ite _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.ite _ body _)))) _))) => body
  | _ => .skip

theorem source_mptInsert_extension_advance : mptInsertExtensionAdvance =
    .seq (.assign .local (ofString "r") (.var .local (ofString "node")))
      (.seq (.assign .local (ofString "next_node") (.load .one (mptInsertNodeAddress 48)))
        (.seq (.assign .local (ofString "next_slot") (mptInsertNodeAddress 48))
          (.seq (.assign .local (ofString "next_level")
            (.op .add [.var .local (ofString "level"),.var .local (ofString "pl")]))
            (.assign .local (ofString "go") (.const 1))))) := by
  simp only [mptInsertExtensionAdvance,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original matching-extension path prepares a live/null child, a typed
positive-extension backlink, and a strictly advanced key level. -/
theorem evaluate_mptInsert_extension_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (registry : TrieWalkRegistry live extensions branches state)
    (node level segment child keyLength : BitVec 64) (registered : node ∈ extensions)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (prefixLocal : state.locals.lookup (ofString "pl") = some (.val (.word segment)))
    (lengthField : state.memory (node + BitVec.ofNat 64 40) = .word segment)
    (childField : state.memory (node + BitVec.ofNat 64 48) = .word child)
    (domain : state.memaddrs (node + BitVec.ofNat 64 48))
    (positive : segment ≠ 0) (fits : level.toNat + segment.toNat ≤ keyLength.toNat)
    (oldResult : BitVec 64) (oldResultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (oldNode : BitVec 64) (oldNodeLocal : state.locals.lookup (ofString "next_node") = some (.val (.word oldNode)))
    (oldSlot : BitVec 64) (oldSlotLocal : state.locals.lookup (ofString "next_slot") = some (.val (.word oldSlot)))
    (oldLevel : BitVec 64) (oldLevelLocal : state.locals.lookup (ofString "next_level") = some (.val (.word oldLevel)))
    (oldGo : BitVec 64) (oldGoLocal : state.locals.lookup (ofString "go") = some (.val (.word oldGo)))
    : ∃ post, evaluateHOLFiniteState state mptInsertExtensionAdvance = (none,post) ∧
      post.locals.lookup (ofString "r") = some (.val (.word node)) ∧
      post.locals.lookup (ofString "next_node") = some (.val (.word child)) ∧ (child = 0 ∨ child ∈ live) ∧
      post.locals.lookup (ofString "next_slot") = some (.val (.word (node + BitVec.ofNat 64 48))) ∧
      TrieChildSlot post extensions branches (node + BitVec.ofNat 64 48) ∧
      post.locals.lookup (ofString "next_level") = some (.val (.word (level + segment))) ∧
      level.toNat < (level + segment).toNat ∧ (level + segment).toNat ≤ keyLength.toNat ∧
      post.locals.lookup (ofString "go") = some (.val (.word (1 : BitVec 64))) ∧
      post.memory = state.memory ∧ post.clock = state.clock := by
  simp [ofString] at nodeLocal levelLocal prefixLocal
  let s1 := setVarHOLFinite (ofString "r") (.val (.word node)) state
  have old0 : state.locals.lookup (ofString "r") = some (.val (.word oldResult)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldResultLocal
  have value0 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "node")) = some (.val (.word node)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertNodeAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,prefixLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField]
  have step0 := evaluate_local_word_assignment state (ofString "r") (.var .local (ofString "node")) oldResult node old0 value0
  let s2 := setVarHOLFinite (ofString "next_node") (.val (.word child)) s1
  have old1 : s1.locals.lookup (ofString "next_node") = some (.val (.word oldNode)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldNodeLocal
  have value1 : @evalHOLExact 64 F _ s1.toExact
      (fun address => Classical.propDecidable (s1.memaddrs address)) (.load .one (mptInsertNodeAddress 48)) = some (.val (.word child)) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertNodeAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,prefixLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField]
    change @memLoadHOLExact 64 _ .one (node + BitVec.ofNat 64 48) state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.memory state.structs = _
    simp [memLoadHOLExact,domain,childField]
  have step1 := evaluate_local_word_assignment s1 (ofString "next_node") (.load .one (mptInsertNodeAddress 48)) oldNode child old1 value1
  let s3 := setVarHOLFinite (ofString "next_slot") (.val (.word (node + BitVec.ofNat 64 48))) s2
  have old2 : s2.locals.lookup (ofString "next_slot") = some (.val (.word oldSlot)) := by
    simpa [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldSlotLocal
  have value2 : @evalHOLExact 64 F _ s2.toExact
      (fun address => Classical.propDecidable (s2.memaddrs address)) (mptInsertNodeAddress 48) = some (.val (.word (node + BitVec.ofNat 64 48))) := by
    simp [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertNodeAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,prefixLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField]
  have step2 := evaluate_local_word_assignment s2 (ofString "next_slot") (mptInsertNodeAddress 48) oldSlot (node + BitVec.ofNat 64 48) old2 value2
  let s4 := setVarHOLFinite (ofString "next_level") (.val (.word (level + segment))) s3
  have old3 : s3.locals.lookup (ofString "next_level") = some (.val (.word oldLevel)) := by
    simpa [s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldLevelLocal
  have value3 : @evalHOLExact 64 F _ s3.toExact
      (fun address => Classical.propDecidable (s3.memaddrs address)) (.op .add [.var .local (ofString "level"),.var .local (ofString "pl")]) = some (.val (.word (level + segment))) := by
    simp [s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertNodeAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,prefixLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField]
  have step3 := evaluate_local_word_assignment s3 (ofString "next_level") (.op .add [.var .local (ofString "level"),.var .local (ofString "pl")]) oldLevel (level + segment) old3 value3
  let s5 := setVarHOLFinite (ofString "go") (.val (.word 1)) s4
  have old4 : s4.locals.lookup (ofString "go") = some (.val (.word oldGo)) := by
    simpa [s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using oldGoLocal
  have value4 : @evalHOLExact 64 F _ s4.toExact
      (fun address => Classical.propDecidable (s4.memaddrs address)) (.const 1) = some (.val (.word 1)) := by
    simp [s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString,
      mptInsertNodeAddress,evalHOLExact,evalListHOLExact,nodeLocal,levelLocal,prefixLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,childField]
  have step4 := evaluate_local_word_assignment s4 (ofString "go") (.const 1) oldGo 1 old4 value4
  have addition : (level + segment).toNat = level.toNat + segment.toNat := by
    rw [BitVec.toNat_add_of_lt (by have bound := keyLength.isLt; omega)]
  have segmentPositive : 0 < segment.toNat := by
    have nonzero : segment.toNat ≠ 0 := fun zero => positive (BitVec.eq_of_toNat_eq zero)
    omega
  refine ⟨s5,?_,?_,?_,registry.extensionChildren node registered child childField,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · rw [source_mptInsert_extension_advance]
    exact evaluate_seq_none step0 (evaluate_seq_none step1 (evaluate_seq_none step2 (evaluate_seq_none step3 step4)))
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · exact Or.inr ⟨node,registered,segment,rfl,lengthField,positive⟩
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · rw [addition]; omega
  · rw [addition]; exact fits
  · simp [s5,s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]

#print axioms source_mptInsert_extension_advance
#print axioms evaluate_mptInsert_extension_advance
end InitECandidate.Runtime
