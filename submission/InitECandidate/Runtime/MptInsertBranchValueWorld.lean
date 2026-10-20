import InitECandidate.Runtime.MptInsertBranchValue
import InitECandidate.Runtime.AllocatedTrieBranchFields
import InitECandidate.Runtime.AllocatedTrieMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual terminal branch-value update earns store domains from the
allocated record and preserves the full world and exact kinds. -/
theorem evaluate_mpt_insert_branch_value_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (node value length oldResult : BitVec 64) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (valueLocal : state.locals.lookup (ofString "vptr") = some (.val (.word value)))
    (lengthLocal : state.locals.lookup (ofString "vlen") = some (.val (.word length)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state mptInsertBranchValue = (none,post) ∧
      AllocatedTrieWorld post live extensions branches size frontier ∧
      TrieNodeKinds post live extensions branches ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "r") = some (.val (.word node)) ∧
      post.memory (node+160)=.word value ∧post.memory (node+168)=.word length ∧
      post.globals=state.globals ∧
      (∀watched : BitVec 64,watched≠node+160→watched≠node+168→post.memory watched=state.memory watched) := by
  have domains (offset : Nat) (inside : offset<176) : state.memaddrs (node+BitVec.ofNat 64 offset) := by
    apply fullDomain
    rw [world.layout.field_nat node (world.layout.branchLive registered) offset (by have:=world.layout.branchSize node registered;omega)]
    have allocated:=world.allocated node (world.layout.branchLive registered)
    have capacity:=world.layout.branchSize node registered
    have capped:=world.capped
    omega
  let s1 := sourceWriteWord state (node + BitVec.ofNat 64 160) value
  let s2 := sourceWriteWord s1 (node + BitVec.ofNat 64 168) length
  have address (current : PanSemStateFiniteExact 64 F) (offset : Nat)
      (binding : current.locals.lookup (ofString "node") = some (.val (.word node))) :
      @evalHOLExact 64 F _ current.toExact (fun address => Classical.propDecidable (current.memaddrs address))
      (mptInsertNodeAddress offset) = some (.val (.word (node + BitVec.ofNat 64 offset))) := by
    simp [mptInsertNodeAddress,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
  have first := evaluate_store_word state (node + BitVec.ofNat 64 160) value _ (.var .local (ofString "vptr"))
    (address state 160 nodeLocal) valueLocal (domains 160 (by decide))
  have second := evaluate_store_word s1 (node + BitVec.ofNat 64 168) length _ (.var .local (ofString "vlen"))
    (address s1 168 nodeLocal) lengthLocal (domains 168 (by decide))
  have assigned := evaluate_local_word_assignment s2 (ofString "r") (.var .local (ofString "node"))
    oldResult node resultLocal nodeLocal
  obtain ⟨world1,kinds1⟩:=world.write_branch_field kinds node value registered 160 (by decide) (by decide)
  obtain ⟨world2,kinds2⟩:=world1.write_branch_field kinds1 node length registered 168 (by decide) (by decide)
  have different : node+160#64≠node+168#64 := by
    intro equal
    have impossible : (160#64)=(168#64):=add_left_cancel equal
    exact (by decide : (160#64)≠(168#64)) impossible
  refine ⟨setVarHOLFinite (ofString "r") (.val (.word node)) s2,?_,world2.after_memory_globals rfl rfl,?_,rfl,?_,?_,?_,rfl,?_⟩
  · rw [source_mptInsert_branch_value]
    exact evaluate_seq_none first (evaluate_seq_none second assigned)
  · exact kinds2.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current registered;rfl)
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change s2.memory (node+160#64)=_
    simp [s2,s1,sourceWriteWord,different]
  · change s2.memory (node+168#64)=_
    simp [s2,sourceWriteWord]
  · intro watched n160 n168
    have a : watched≠node+160#64:=n160
    have b : watched≠node+168#64:=n168
    change s2.memory watched=_
    simp [s2,s1,sourceWriteWord,a,b]

#print axioms evaluate_mpt_insert_branch_value_world
end InitECandidate.Runtime
