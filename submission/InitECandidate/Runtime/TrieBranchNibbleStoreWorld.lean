import InitECandidate.Runtime.TrieBranchNibbleStore
import InitECandidate.Runtime.AllocatedTrieChildKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real nibble-indexed branch store earns its physical slot from the
actual loaded nibble and record extent, preserving allocated world and kinds. -/
theorem evaluate_branch_nibble_store_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (branchName bufferName indexName childName : MlS)
    (parent buffer index length child : BitVec 64) (byte : UInt8)
    (branchLocal : state.locals.lookup branchName = some (.val (.word parent)))
    (bufferLocal : state.locals.lookup bufferName = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup indexName = some (.val (.word index)))
    (childLocal : state.locals.lookup childName = some (.val (.word child)))
    (registered : parent ∈ branches) (childValid : child = 0 ∨ child ∈ live)
    (inside : index.toNat < length.toNat) (nibbles : TrieNibbleRange state buffer length)
    (read : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (buffer + index) = some byte)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (branchNibbleStore branchName bufferName indexName childName) = (none,post) ∧
      AllocatedTrieWorld post live extensions branches size frontier ∧
      TrieNodeKinds post live extensions branches ∧ post.clock = state.clock ∧ post.locals = state.locals ∧
      post.memory (branchChildAddress parent byte.toNat) = .word child ∧post.globals=state.globals ∧
      (∀watched,watched≠branchChildAddress parent byte.toNat→post.memory watched=state.memory watched) := by
  have small : byte.toNat < 16 := nibbles index.toNat inside byte (by simpa using read)
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local branchName,.const 32,
        .panop .mul [.loadByte (.op .add [.var .local bufferName,.var .local indexName]),.const 8]]) =
      some (.val (.word (branchChildAddress parent byte.toNat))) := by
    simp [evalHOLExact,evalListHOLExact,branchLocal,bufferLocal,indexLocal,read,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,branchChildAddress,BitVec.add_assoc]
  have domain : state.memaddrs (branchChildAddress parent byte.toNat) := by
    apply fullDomain
    have addressNat : branchChildAddress parent byte.toNat=parent+BitVec.ofNat 64 (32+byte.toNat*8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
    rw [addressNat,world.layout.field_nat parent (world.layout.branchLive registered) _
      (by have:=world.layout.branchSize parent registered;omega)]
    have allocated:=world.allocated parent (world.layout.branchLive registered)
    have capacity:=world.layout.branchSize parent registered
    have capped:=world.capped
    omega
  have store := evaluate_store_word state (branchChildAddress parent byte.toNat) child _ (.var .local childName)
    address childLocal domain
  obtain ⟨worldOut,kindsOut⟩:=world.write_branch_child_kinds kinds parent child registered byte.toNat small childValid
  refine ⟨sourceWriteWord state (branchChildAddress parent byte.toNat) child,store,
    worldOut,kindsOut,rfl,rfl,?_,rfl,?_⟩
  · simp [sourceWriteWord]
  · intro watched different
    simp [sourceWriteWord,different]

#print axioms evaluate_branch_nibble_store_world
end InitECandidate.Runtime
