import InitECandidate.Runtime.HashTableReadyByteOutside32
import InitECandidate.Runtime.HashDeleteFinalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original deletion occupancy clear preserves every disjoint ready table. -/
theorem evaluate_hashDelete_clear_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base length hole cell : BitVec 64)
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word base)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (domain : state.memaddrs (panByteAlignHOL (base + hole)))
    (memory : state.memory (panByteAlignHOL (base + hole)) = .word cell)
    (inside : hole.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (separate : base.toNat + length.toNat ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ base.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteClear = (none,post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  refine ⟨sourceWriteByte state (base + hole) 0 cell,
    (evaluate_hashDelete_clear state base hole cell usedLocal holeLocal domain memory).1, ?_,
    rfl,rfl,rfl,rfl,rfl,rfl⟩
  exact ready.after_array_byte state table pointer keys stride capacity used values order orderPos items base length hole 0 cell bits
    inside aligned bounded separate

#print axioms evaluate_hashDelete_clear_other
end InitECandidate.Runtime
