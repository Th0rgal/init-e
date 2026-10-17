import InitECandidate.Runtime.HashDeleteGuardLinked32
import InitECandidate.Runtime.HashDeleteHeaderScopesValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem HashTableArraysInvariant.delete_guarded_headers_from_hole_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
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
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have different : hole ≠ capacity := by intro equal; subst hole; omega
  obtain ⟨post,run,postRegistered,cost,remaining,globals,code,domain,endian⟩ := invariant.delete_header_scopes_from_hole_values_in state
    keyLength table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder holeInside holeOccupied
    holeLocal capacityLocal linked tableLocal supported targets registered budget
  refine ⟨post,?_,postRegistered,cost,remaining,globals,code,domain,endian⟩
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_found state hole capacity different holeLocal capacityLocal]
  exact run

#print axioms HashTableArraysInvariant.delete_guarded_headers_from_hole_values_in
end InitECandidate.Runtime
