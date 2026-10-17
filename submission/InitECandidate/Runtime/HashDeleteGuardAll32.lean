import InitECandidate.Runtime.HashDeleteGuardLinked32
import InitECandidate.Runtime.HashDeleteHeaderScopesAll32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem HashTableArraysInvariant32.delete_all_guarded_headers_from_hole {F : Type}
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
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (items - 1) bits post ∧
      HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity (items - 1) post ∧
      HashReverseEntriesBound used orderPos capacity (items - 1) post ∧ HashOrderLinked used order orderPos capacity (items - 1) post := by
  have different : hole ≠ capacity := by intro equal; subst hole; omega
  obtain ⟨post,run,cost,remaining,arrays,words,orderEntries,reverseEntries,postLinked⟩ := invariant.delete_all_header_scopes_from_hole state
    table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder holeInside holeOccupied
    holeLocal capacityLocal linked tableLocal budget
  refine ⟨post,?_,cost,remaining,arrays,words,orderEntries,reverseEntries,postLinked⟩
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_found state hole capacity different holeLocal capacityLocal]
  exact run

#print axioms HashTableArraysInvariant32.delete_all_guarded_headers_from_hole
end InitECandidate.Runtime
