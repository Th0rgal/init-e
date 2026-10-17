import InitECandidate.Runtime.HashDeleteGuardLinked32
import InitECandidate.Runtime.HashDeleteHeaderScopesOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem HashTableArraysInvariant32.delete_guarded_headers_with_other_from_hole {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (holeInside : hole.toNat < capacity.toNat)
    (holeOccupied : hashOccupancyRead state used hole ≠ some 0)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have different : hole ≠ capacity := by intro equal; subst hole; omega
  obtain ⟨post,run,preserved,cost,remaining,globals,code,domain,endian⟩ := invariant.delete_header_scopes_with_other_from_hole state
    table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder holeInside holeOccupied
    holeLocal capacityLocal linked tableLocal
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separated budget
  refine ⟨post,?_,preserved,cost,remaining,globals,code,domain,endian⟩
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_found state hole capacity different holeLocal capacityLocal]
  exact run

#print axioms HashTableArraysInvariant32.delete_guarded_headers_with_other_from_hole
end InitECandidate.Runtime
