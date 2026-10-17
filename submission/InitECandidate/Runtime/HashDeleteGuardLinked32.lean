import InitECandidate.Runtime.HashDeleteHeaderSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashDeleteMissingGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "i")) (.var .local (ofString "cap"))) (.return (.const 0)) .skip

theorem evaluate_hashDelete_guard_found {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hole capacity : BitVec 64) (different : hole ≠ capacity)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    evaluateHOLFiniteState state hashDeleteMissingGuard = (none,state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "i")) (.var .local (ofString "cap"))) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,holeLocal,capacityLocal,Compiler.Encoders.Asm.wordCmpHOL,different]
  unfold hashDeleteMissingGuard
  rw [evaluateHOLFiniteState_ite,condition]
  exact evaluateHOLFiniteState_skip state

theorem evaluate_hashDelete_guard_missing {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity : BitVec 64)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word capacity)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    evaluateHOLFiniteState state hashDeleteMissingGuard =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "i")) (.var .local (ofString "cap"))) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,holeLocal,capacityLocal,Compiler.Encoders.Asm.wordCmpHOL]
  unfold hashDeleteMissingGuard
  rw [evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

theorem HashTableArraysInvariant32.delete_linked_guarded_headers_from_hole {F : Type}
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
      HashOrderLinked used order orderPos capacity (items - 1) post := by
  have different : hole ≠ capacity := by intro equal; subst hole; omega
  obtain ⟨post,run,cost,remaining,postLinked⟩ := invariant.delete_linked_header_scopes_from_hole state
    table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder holeInside holeOccupied
    holeLocal capacityLocal linked tableLocal budget
  refine ⟨post,?_,cost,remaining,postLinked⟩
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_found state hole capacity different holeLocal capacityLocal]
  exact run

#print axioms evaluate_hashDelete_guard_found
#print axioms evaluate_hashDelete_guard_missing
#print axioms HashTableArraysInvariant32.delete_linked_guarded_headers_from_hole
end InitECandidate.Runtime
