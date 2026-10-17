import InitECandidate.Runtime.TrieNodeLayout
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def branchNibbleStore (branch buffer index child : MlS) : ProgHOL 64 :=
  .store (.op .add [.var .local branch,.const 32,
    .panop .mul [.loadByte (.op .add [.var .local buffer,.var .local index]),.const 8]])
    (.var .local child)

/-- The actual nibble-indexed source store selects a branch child slot from
its loaded byte. Range validity supplies the sixteen-slot bound. -/
theorem evaluate_branchNibble_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
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
    (domain : ∀ slot : Nat, slot < 16 → state.memaddrs (branchChildAddress parent slot)) :
    ∃ post, evaluateHOLFiniteState state (branchNibbleStore branchName bufferName indexName childName) = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧ post.locals = state.locals ∧
      post.memory (branchChildAddress parent byte.toNat) = .word child := by
  have small : byte.toNat < 16 := nibbles index.toNat inside byte (by simpa using read)
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local branchName,.const 32,
        .panop .mul [.loadByte (.op .add [.var .local bufferName,.var .local indexName]),.const 8]]) =
      some (.val (.word (branchChildAddress parent byte.toNat))) := by
    simp [evalHOLExact,evalListHOLExact,branchLocal,bufferLocal,indexLocal,read,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,branchChildAddress,BitVec.add_assoc]
  have store := evaluate_store_word state (branchChildAddress parent byte.toNat) child _ (.var .local childName)
    address childLocal (domain byte.toNat small)
  refine ⟨sourceWriteWord state (branchChildAddress parent byte.toNat) child,store,
    registry.write_branch_slot state live extensions branches size layout parent child registered byte.toNat small childValid,rfl,rfl,?_⟩
  simp [sourceWriteWord]

def splitExtensionFirstChildStore : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__split_extension with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.seq (.ite _ body _) _))))) => body
  | _ => .skip

theorem source_splitExtension_first_child_store : splitExtensionFirstChildStore =
    branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "child") := by
  simp only [splitExtensionFirstChildStore,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms evaluate_branchNibble_store
#print axioms source_splitExtension_first_child_store
end InitECandidate.Runtime
