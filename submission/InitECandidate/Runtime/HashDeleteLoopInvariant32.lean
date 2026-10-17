import InitECandidate.Runtime.HashDeleteLoopRanked
import InitECandidate.Runtime.HashDeleteEmptyIteration32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts retained while scanning a deletion cluster; the empty witness is
fixed while both hole and scan locals may advance. -/
structure HashDeleteLoopInvariant32 {F : Type}
    (table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  arrays : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state
  valuesWord : HashValueEntriesWord used values capacity state
  reverse : HashReverseEntriesBound used orderPos capacity items state
  ordered : HashOrderEntriesBound order capacity items state
  keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat
  emptyInside : empty.toNat < capacity.toNat
  emptyRead : hashOccupancyRead state used empty = some 0
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64)))
  capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values))
  orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order))
  reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))
  indices : ∃ hole index : BitVec 64, hole.toNat < capacity.toNat ∧ index.toNat < capacity.toNat ∧
    state.locals.lookup (ofString "i") = some (.val (.word hole)) ∧
    state.locals.lookup (ofString "j") = some (.val (.word index))

noncomputable def hashDeleteStateRank {F : Type} (capacity empty : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "j") with
  | some (.val (.word index)) => hashDeleteRank capacity index empty
  | _ => 0

theorem hashDeleteStateRank_of_local {F : Type} (capacity empty index : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (binding : state.locals.lookup (ofString "j") = some (.val (.word index))) :
    hashDeleteStateRank capacity empty state = hashDeleteRank capacity index empty := by
  simp [hashDeleteStateRank,binding]

theorem HashDeleteLoopInvariant32.rank_bounds {F : Type}
    (table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state) :
    0 < hashDeleteStateRank capacity empty state ∧ hashDeleteStateRank capacity empty state ≤ capacity.toNat := by
  obtain ⟨hole,index,_,inside,_,binding⟩ := valid.indices
  rw [hashDeleteStateRank_of_local capacity empty index state binding]
  exact hashDeleteRank_bounded capacity index empty bits valid.arrays.power inside valid.emptyInside

theorem HashDeleteLoopInvariant32.dec_clock {F : Type}
    (table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state) :
    HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits (decClockHOLFinite state) := by
  exact {
    valid with
    arrays := valid.arrays.after_read state _ table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
    valuesWord := valid.valuesWord.after_read state _ used values capacity rfl rfl rfl
    reverse := valid.reverse.after_read state _ used orderPos capacity items rfl rfl rfl
    ordered := valid.ordered.after_memory state _ order capacity items rfl
  }

theorem hashDeleteStateRank_dec_clock {F : Type} (capacity empty : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) :
    hashDeleteStateRank capacity empty (decClockHOLFinite state) = hashDeleteStateRank capacity empty state := rfl

#print axioms hashDeleteStateRank_of_local
#print axioms HashDeleteLoopInvariant32.rank_bounds
#print axioms HashDeleteLoopInvariant32.dec_clock
#print axioms hashDeleteStateRank_dec_clock
end InitECandidate.Runtime
