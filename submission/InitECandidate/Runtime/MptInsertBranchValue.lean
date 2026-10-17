import InitECandidate.Runtime.TrieBranchValueStore
import InitECandidate.Runtime.HashWordStep
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertLoopStep : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__mpt_insert_node with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _))) => body
  | _ => .skip

def mptInsertKindDispatch : ProgHOL 64 :=
  match mptInsertLoopStep with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.seq _ (.seq (.ite _ _ (.dec _ _ _ body)) _))))) => body
  | _ => .skip

def mptInsertBranchValue : ProgHOL 64 :=
  match mptInsertKindDispatch with
  | .seq _ (.seq _ (.ite _ _ (.ite _ _ (.ite _ body _)))) => body
  | _ => .skip

def mptInsertNodeAddress (offset : Nat) : ExpHOL 64 :=
  .op .add [.var .local (ofString "node"),.const (BitVec.ofNat 64 offset)]

theorem source_mptInsert_branch_value : mptInsertBranchValue =
    .seq (.store (mptInsertNodeAddress 160) (.var .local (ofString "vptr")))
      (.seq (.store (mptInsertNodeAddress 168) (.var .local (ofString "vlen")))
        (.assign .local (ofString "r") (.var .local (ofString "node")))) := by
  simp only [mptInsertBranchValue,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original insertion branch-value update preserves the traversal
registry and returns the existing live branch through local r. -/
theorem evaluate_mptInsert_branch_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (node value length oldResult : BitVec 64) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (valueLocal : state.locals.lookup (ofString "vptr") = some (.val (.word value)))
    (lengthLocal : state.locals.lookup (ofString "vlen") = some (.val (.word length)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (valueDomain : state.memaddrs (node + BitVec.ofNat 64 160))
    (lengthDomain : state.memaddrs (node + BitVec.ofNat 64 168)) :
    ∃ post, evaluateHOLFiniteState state mptInsertBranchValue = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "r") = some (.val (.word node)) := by
  let s1 := sourceWriteWord state (node + BitVec.ofNat 64 160) value
  let s2 := sourceWriteWord s1 (node + BitVec.ofNat 64 168) length
  have address (current : PanSemStateFiniteExact 64 F) (offset : Nat)
      (binding : current.locals.lookup (ofString "node") = some (.val (.word node))) :
      @evalHOLExact 64 F _ current.toExact (fun address => Classical.propDecidable (current.memaddrs address))
      (mptInsertNodeAddress offset) = some (.val (.word (node + BitVec.ofNat 64 offset))) := by
    simp [mptInsertNodeAddress,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
  have first := evaluate_store_word state (node + BitVec.ofNat 64 160) value _ (.var .local (ofString "vptr"))
    (address state 160 nodeLocal) valueLocal valueDomain
  have second := evaluate_store_word s1 (node + BitVec.ofNat 64 168) length _ (.var .local (ofString "vlen"))
    (address s1 168 nodeLocal) lengthLocal lengthDomain
  have assigned := evaluate_local_word_assignment s2 (ofString "r") (.var .local (ofString "node"))
    oldResult node resultLocal nodeLocal
  have r1 : TrieWalkRegistry live extensions branches s1 :=
    registry.write_branch_value state live extensions branches size layout node value registered 160 (by decide) (by decide)
  have r2 : TrieWalkRegistry live extensions branches s2 :=
    r1.write_branch_value s1 live extensions branches size layout node length registered 168 (by decide) (by decide)
  refine ⟨setVarHOLFinite (ofString "r") (.val (.word node)) s2,?_,r2.after_memory rfl,rfl,?_⟩
  · rw [source_mptInsert_branch_value]
    exact evaluate_seq_none first (evaluate_seq_none second assigned)
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms source_mptInsert_branch_value
#print axioms evaluate_mptInsert_branch_value
end InitECandidate.Runtime
