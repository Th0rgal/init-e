import InitECandidate.Runtime.MptInsertCommit
import InitECandidate.Runtime.TrieChildSlotPathsWorld
import InitECandidate.Runtime.TrieChildSlotMetadataSeparation
import InitECandidate.Runtime.TrieNodePathsContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual commit either assigns its live root or updates a typed child
link. Allocation geometry earns store readability and preserves all paths. -/
theorem evaluate_mpt_insert_commit_paths_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (slot result oldRoot : BitVec 64)
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (rootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address) :
    ∃ post root, evaluateHOLFiniteState state mptInsertCommit = (none,post) ∧
      AllocatedTrieWorld post live extensions branches size frontier ∧
      TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier ∧
      post.clock=state.clock ∧
      post.locals.lookup (ofString "result") = some (.val (.word root)) ∧ (root = 0 ∨ root ∈ live) ∧
      (∀key len,TriePathBuffer state live size key len frontier→TriePathBuffer post live size key len frontier) := by
 rw [source_mptInsert_commit,evaluateHOLFiniteState_ite]
 by_cases zero : slot=0
 · have guard : @evalHOLExact 64 F _ state.toExact
    (fun address=>Classical.propDecidable (state.memaddrs address))
    (.cmp .equal (.var .local (ofString "slot")) (.const 0))=some (.val (.word (1#64))) := by
    simp [evalHOLExact,slotLocal,zero,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard]
   have assignment:=evaluate_local_word_assignment state (ofString "result") (.var .local (ofString "r"))
    oldRoot result rootLocal resultLocal
   refine ⟨setVarHOLFinite (ofString "result") (.val (.word result)) state,result,by simpa using assignment,
    world.after_memory_globals rfl rfl,?_,paths.after_context rfl rfl rfl,rfl,?_,resultValid,?_⟩
   · exact kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · intro key len path;exact path.after_context rfl rfl rfl
 · have guard : @evalHOLExact 64 F _ state.toExact
    (fun address=>Classical.propDecidable (state.memaddrs address))
    (.cmp .equal (.var .local (ofString "slot")) (.const 0))=some (.val (.word (0#64))) := by
    simp [evalHOLExact,slotLocal,Compiler.Encoders.Asm.wordCmpHOL]
    exact zero
   rw [guard]
   have domain : state.memaddrs slot := by
    apply fullDomain
    have below:=(typedSlot zero).allocated_below state live extensions branches size frontier slot world
    have:=world.capped;omega
   have stored:=evaluate_store_word state slot result (.var .local (ofString "slot")) (.var .local (ofString "r"))
    slotLocal resultLocal domain
   obtain ⟨worldOut,kindsOut,pathsOut,transport⟩:=(typedSlot zero).write_paths_world world kinds paths result resultValid
   exact ⟨sourceWriteWord state slot result,oldRoot,stored,worldOut,kindsOut,pathsOut,rfl,rootLocal,rootValid,transport⟩

#print axioms evaluate_mpt_insert_commit_paths_world
end InitECandidate.Runtime
