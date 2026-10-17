import InitECandidate.Runtime.HashDeleteLoopInvariant32
import InitECandidate.Runtime.HashDeleteClearCount
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashDeleteLoopInvariant32.clear {F : Type}
    (table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state) :
    ∃ post, evaluateHOLFiniteState state hashDeleteClear = (none,post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) + 1 = items.toNat ∧
      post.clock = state.clock := by
  obtain ⟨hole,_,inside,_,holeLocal,_,occupied⟩ := valid.indices
  have facts := valid.arrays.insertion_memory state table keys stride capacity used values order orderPos items bits
  obtain ⟨cell,memory⟩ : ∃ cell : BitVec 64, state.memory (panByteAlignHOL (used + hole)) = .word cell := by
    cases state.memory (panByteAlignHOL (used + hole)) with | word cell => exact ⟨cell,rfl⟩
  have run := (evaluate_hashDelete_clear state used hole cell valid.usedLocal holeLocal (facts.byteDomain hole inside) memory).1
  have count := sourceWriteByte_occupancy_clear state capacity used hole cell inside (facts.byteDomain hole inside) memory occupied
  exact ⟨_,run,count.trans valid.arrays.agreement.symm,rfl⟩

#print axioms HashDeleteLoopInvariant32.clear
end InitECandidate.Runtime
