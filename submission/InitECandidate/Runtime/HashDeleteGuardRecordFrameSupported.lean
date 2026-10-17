import InitECandidate.Runtime.HashDeleteGuardLinked32
import InitECandidate.Runtime.HashDeleteHeaderScopesRecordFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem HashTableArraysInvariant.delete_guarded_headers_with_record_frame_from_hole_supported {F : Type}
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
    (journal : BitVec 64) (journalCount : Nat)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + journalCount * 32 ≤ table.toNat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have different : hole ≠ capacity := by intro equal; subst hole; omega
  obtain ⟨post,run,preserved,cost,remaining,globals,code,domain,endian⟩ := invariant.delete_header_scopes_with_record_frame_from_hole_supported state
    keyLength table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder holeInside holeOccupied
    holeLocal capacityLocal linked tableLocal
    journal journalCount journalBound separated supported budget
  refine ⟨post,?_,preserved,cost,remaining,globals,code,domain,endian⟩
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_found state hole capacity different holeLocal capacityLocal]
  exact run

#print axioms HashTableArraysInvariant.delete_guarded_headers_with_record_frame_from_hole_supported
end InitECandidate.Runtime
