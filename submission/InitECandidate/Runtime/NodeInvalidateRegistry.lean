import InitECandidate.Runtime.TrieNodeMetadataStore
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodeInvalidateAddress (offset : Nat) : ExpHOL 64 :=
  .op .add [.var .local (ofString "nd"),.const (BitVec.ofNat 64 offset)]

theorem source_nodeInvalidate_body : sourceFunctionBody Guest.guestFn_node_invalidate =
    .seq (.store (nodeInvalidateAddress 8) (.const 0))
      (.seq (.store (nodeInvalidateAddress 16) (.const 0))
        (.seq (.store (nodeInvalidateAddress 24) (.const 0)) (.return (.const 0)))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original cache invalidation preserves the traversal registry and spends
no source clock, at every starting fuel value. -/
theorem evaluate_nodeInvalidate_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (pointer : BitVec 64) (member : pointer ∈ live) (capacity : 32 ≤ size pointer)
    (binding : state.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (domain : ∀ offset ∈ ([8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_invalidate) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock := by
  let s1 := sourceWriteWord state (pointer + BitVec.ofNat 64 8) 0
  let s2 := sourceWriteWord s1 (pointer + BitVec.ofNat 64 16) 0
  let s3 := sourceWriteWord s2 (pointer + BitVec.ofNat 64 24) 0
  have address (current : PanSemStateFiniteExact 64 F) (offset : Nat)
      (binding : current.locals.lookup (ofString "nd") = some (.val (.word pointer))) :
      @evalHOLExact 64 F _ current.toExact (fun address => Classical.propDecidable (current.memaddrs address))
        (nodeInvalidateAddress offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
    simp [nodeInvalidateAddress,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
  have first := evaluate_store_word state (pointer + BitVec.ofNat 64 8) 0 _ (.const 0)
    (address state 8 binding) rfl (domain 8 (by simp))
  have second := evaluate_store_word s1 (pointer + BitVec.ofNat 64 16) 0 _ (.const 0)
    (address s1 16 binding) rfl (domain 16 (by simp))
  have third := evaluate_store_word s2 (pointer + BitVec.ofNat 64 24) 0 _ (.const 0)
    (address s2 24 binding) rfl (domain 24 (by simp))
  have returned : evaluateHOLFiniteState s3 (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite s3) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have r1 : TrieWalkRegistry live extensions branches s1 :=
    registry.write_metadata state live extensions branches size layout pointer 0 member capacity 8 (by decide) (by decide)
  have r2 : TrieWalkRegistry live extensions branches s2 :=
    r1.write_metadata s1 live extensions branches size layout pointer 0 member capacity 16 (by decide) (by decide)
  have r3 : TrieWalkRegistry live extensions branches s3 :=
    r2.write_metadata s2 live extensions branches size layout pointer 0 member capacity 24 (by decide) (by decide)
  refine ⟨emptyLocalsHOLFinite s3,?_,r3.after_memory rfl,rfl⟩
  rw [source_nodeInvalidate_body]
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third returned))

#print axioms source_nodeInvalidate_body
#print axioms evaluate_nodeInvalidate_registry
end InitECandidate.Runtime
