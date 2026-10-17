import InitECandidate.Runtime.HashDeleteLinkedLoopMetadata32
import InitECandidate.Runtime.HashDeleteLoopOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Linked final-hole information and another table survive the same actual scan. -/
theorem evaluate_hashDelete_linked_loop_other32 {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLinkedLoopExit32 table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,exitValid,cost,remaining,globals,code,domain,endian⟩ := evaluate_hashDelete_linked_loop_metadata32
    table keys stride capacity used values order orderPos items empty deletedPosition bits state valid budget
  obtain ⟨checked,checkedRun,⟨_,preserved⟩,_,_⟩ := evaluate_hashDelete_loop_other32
    table keys stride capacity used values order orderPos items empty bits state valid.base
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits ready separated budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,exitValid,by rw [same]; exact preserved,cost,remaining,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_linked_loop_other32
end InitECandidate.Runtime
