import InitECandidate.Runtime.TrieBranchNibbleStore
import InitECandidate.Runtime.AllocatedTrieChildKinds
import InitECandidate.Runtime.TrieNodePathsStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def branchSlotStore (branch slot child : MlS) : ProgHOL 64 :=
 .store (.op .add [.var .local branch,.const 32,
  .panop .mul [.var .local slot,.const 8]]) (.var .local child)

/-- The real branch store uses the word already bound by the original
nibble declaration and earns its physical address from the record extent, preserving allocated world and kinds. -/
theorem evaluate_branch_slot_store_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (branchName slotName childName : MlS)
    (parent slot child : BitVec 64)
    (branchLocal : state.locals.lookup branchName = some (.val (.word parent)))
    (slotLocal : state.locals.lookup slotName = some (.val (.word slot)))
    (childLocal : state.locals.lookup childName = some (.val (.word child)))
    (registered : parent ∈ branches) (childValid : child = 0 ∨ child ∈ live)
    (small : slot.toNat < 16)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (branchSlotStore branchName slotName childName) = (none,post) ∧
      AllocatedTrieWorld post live extensions branches size frontier ∧
      TrieNodeKinds post live extensions branches ∧
      TrieNodePaths post live extensions branches size frontier ∧ post.clock = state.clock ∧ post.locals = state.locals ∧
      post.memory (branchChildAddress parent slot.toNat) = .word child ∧post.globals=state.globals ∧
      (∀watched,watched≠branchChildAddress parent slot.toNat→post.memory watched=state.memory watched) ∧
      (∀key len,TriePathBuffer state live size key len frontier→TriePathBuffer post live size key len frontier) := by
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local branchName,.const 32,
        .panop .mul [.var .local slotName,.const 8]]) =
      some (.val (.word (branchChildAddress parent slot.toNat))) := by
    simp [evalHOLExact,evalListHOLExact,branchLocal,slotLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,branchChildAddress,BitVec.add_assoc]
  have domain : state.memaddrs (branchChildAddress parent slot.toNat) := by
    apply fullDomain
    have addressNat : branchChildAddress parent slot.toNat=parent+BitVec.ofNat 64 (32+slot.toNat*8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
    rw [addressNat,world.layout.field_nat parent (world.layout.branchLive registered) _
      (by have:=world.layout.branchSize parent registered;omega)]
    have allocated:=world.allocated parent (world.layout.branchLive registered)
    have capacity:=world.layout.branchSize parent registered
    have capped:=world.capped
    omega
  have store := evaluate_store_word state (branchChildAddress parent slot.toNat) child _ (.var .local childName)
    address childLocal domain
  obtain ⟨worldOut,kindsOut⟩:=world.write_branch_child_kinds kinds parent child registered slot.toNat small childValid
  refine ⟨sourceWriteWord state (branchChildAddress parent slot.toNat) child,store,
    worldOut,kindsOut,?_,rfl,rfl,?_,rfl,?_,?_⟩
  · have addressNat : branchChildAddress parent slot.toNat=parent+BitVec.ofNat 64 (32+slot.toNat*8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
    rw [addressNat]
    exact paths.after_node_field world parent child (world.layout.branchLive registered) _
      (by have:=world.layout.branchSize parent registered;omega) (Or.inl registered)
  · simp [sourceWriteWord]
  · intro watched different
    simp [sourceWriteWord,different]

  · intro key len path
    have addressNat : branchChildAddress parent slot.toNat=parent+BitVec.ofNat 64 (32+slot.toNat*8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
    rw [addressNat]
    exact path.after_node_field world.layout parent child (world.layout.branchLive registered) _
      (by have:=world.layout.branchSize parent registered;omega)

#print axioms evaluate_branch_slot_store_world
end InitECandidate.Runtime
