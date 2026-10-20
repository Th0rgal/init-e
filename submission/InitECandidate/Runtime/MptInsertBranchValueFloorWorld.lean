import InitECandidate.Runtime.TrieAllocationFloorFrame
import InitECandidate.Runtime.MptInsertBranchValueWorld
import InitECandidate.Runtime.TrieNodePathsFrame
import InitECandidate.Runtime.MptInsertLeafMatchedTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual normal branch payload stores preserve all stored paths and any
separated insertion key. No future store/frame callback is assumed. -/
theorem mpt_insert_branch_value_normal_floor_world {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (floor : Nat) (lower : TrieAllocationFloor state live branches floor)
    (node value length oldResult : BitVec 64) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (valueLocal : state.locals.lookup (ofString "vptr") = some (.val (.word value)))
    (lengthLocal : state.locals.lookup (ofString "vlen") = some (.val (.word length)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address)
    (run : evaluateHOLFiniteState state mptInsertBranchValue=(none,post)) :
    AllocatedTrieWorld post live extensions branches size frontier ∧
    TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier ∧
    post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
    TrieAllocationFloor post live branches floor ∧
    (∀key keyLength,TriePathBuffer state live size key keyLength frontier→
      TriePathBuffer post live size key keyLength frontier) := by
 obtain ⟨actual,evaluated,worldOut,kindsOut,_,result,_,_,_,frame⟩:=
  evaluate_mpt_insert_branch_value_world state live extensions branches size frontier world kinds
   node value length oldResult registered nodeLocal valueLocal lengthLocal resultLocal fullDomain
 have equal : actual=post:=(Prod.mk.inj (evaluated.symm.trans run)).2
 subst actual
 have metadata:=evaluateHOLFiniteState_metadata state mptInsertBranchValue
 rw [run] at metadata
 have member:=world.layout.branchLive registered
 have inside (field : Nat) (included : field∈[160,168]) : field<size node := by
  have capacity:=world.layout.branchSize node registered
  simp only [List.mem_cons,List.not_mem_nil,or_false] at included
  rcases included with rfl|rfl <;>omega
 have fieldsFrame (watched : BitVec 64)
  (separate : ∀field∈[160,168],watched≠node+BitVec.ofNat 64 field) :
  post.memory watched=state.memory watched :=
  frame watched (separate 160 (by simp)) (separate 168 (by simp))
 have lowerOut:=lower.after_record_fields paths world node member [160,168] inside (Or.inl registered) fieldsFrame
 refine ⟨worldOut,kindsOut,?_,result,lowerOut,?_⟩
 · exact paths.after_record_fields world node member [160,168] inside (Or.inl registered)
    fieldsFrame metadata.2.1 metadata.2.2.1
 · intro key keyLength path
   exact path.after_record_fields world node member [160,168] inside fieldsFrame metadata.2.1 metadata.2.2.1

#print axioms mpt_insert_branch_value_normal_floor_world
end InitECandidate.Runtime
