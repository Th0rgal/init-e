import InitECandidate.Runtime.MptInsertCommitFloorWorld
import InitECandidate.Runtime.MptInsertAdvanceFrame
import InitECandidate.Runtime.MptInsertFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete normal finish: commit followed by the actual traversal assignments.
No idempotent-backlink assumption is needed; a new live root is allowed. -/
theorem mpt_insert_finish_normal_allocation_floor {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (floor : Nat) (lower : TrieAllocationFloor state live branches floor)
    (slot result oldRoot : BitVec 64)
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (rootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address)
    (run : evaluateHOLFiniteState state mptInsertFinish=(none,post)) :
    TrieAllocationFloor post live branches floor := by
 rw [source_mptInsert_finish] at run
 obtain ⟨middle,commit,advance⟩:=seq_normal_parts run
 obtain ⟨actual,root,evaluated,worldOut,kindsOut,pathsOut,lowerOut,_,rootAt,rootValid,transport⟩:=
  evaluate_mpt_insert_commit_floor_world state live extensions branches size frontier world kinds paths
   floor lower slot result oldRoot slotLocal resultLocal rootLocal resultValid rootValid typedSlot fullDomain
 have same : actual=middle:=(Prod.mk.inj (evaluated.symm.trans commit)).2
 subst actual
 obtain ⟨memory,globals⟩:=mpt_insert_advance_normal_frame middle post advance
 exact lowerOut.after_memory memory

#print axioms mpt_insert_finish_normal_allocation_floor
end InitECandidate.Runtime
