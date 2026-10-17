import InitECandidate.Runtime.HashDeleteHashNoMove32
import InitECandidate.Runtime.HashTableReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hashing without movement preserves an arbitrary ready table. -/
theorem evaluate_hashDelete_hash_no_move_other32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride hole capacity : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : (keys + index * stride).toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (table pointer otherKeys otherStride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (valid : HashTableReady32 table otherKeys otherStride otherCapacity used values order orderPos items bits pointer state) :
    ∃ hash : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableReady32 table otherKeys otherStride otherCapacity used values order orderPos items bits pointer ready ∧
      (¬ hashDeleteMoveRequired hole index (hash &&& (capacity - 1)) →
        evaluateHOLFiniteState state hashDeleteLoopRest = (none,ready)) := by
  obtain ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,run⟩ :=
    evaluate_hashDelete_hash_no_move32 state keys index stride hole capacity keysLocal indexLocal strideLocal lengthLocal holeLocal capacityLocal code clock aligned domain
  exact ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,
    valid.after_read state ready table otherKeys otherStride otherCapacity used values order orderPos items bits pointer memory globals postCode addresses endian,run⟩

#print axioms evaluate_hashDelete_hash_no_move_other32
end InitECandidate.Runtime
