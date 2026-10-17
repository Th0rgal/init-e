import InitECandidate.Runtime.HashDeleteLoopInvariant32
import InitECandidate.Runtime.HashDeleteEmptyIterationWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts retained while scanning a deletion cluster; the empty witness is
fixed while both hole and scan locals may advance. -/
structure HashDeleteLoopInvariantWidth {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state
  valuesWord : HashValueEntriesWord used values capacity state
  reverse : HashReverseEntriesBound used orderPos capacity items state
  ordered : HashOrderEntriesBound order capacity items state
  keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat
  emptyInside : empty.toNat < capacity.toNat
  emptyRead : hashOccupancyRead state used empty = some 0
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))
  capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values))
  orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order))
  reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))
  indices : ∃ hole index : BitVec 64, hole.toNat < capacity.toNat ∧ index.toNat < capacity.toNat ∧
    state.locals.lookup (ofString "i") = some (.val (.word hole)) ∧
    state.locals.lookup (ofString "j") = some (.val (.word index)) ∧ hashOccupancyRead state used hole ≠ some 0

theorem HashDeleteLoopInvariantWidth.rank_bounds {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state) :
    0 < hashDeleteStateRank capacity empty state ∧ hashDeleteStateRank capacity empty state ≤ capacity.toNat := by
  obtain ⟨hole,index,_,inside,_,binding,_⟩ := valid.indices
  rw [hashDeleteStateRank_of_local capacity empty index state binding]
  exact hashDeleteRank_bounded capacity index empty bits valid.arrays.power inside valid.emptyInside

theorem HashDeleteLoopInvariantWidth.dec_clock {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state) :
    HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits (decClockHOLFinite state) := by
  exact {
    valid with
    arrays := valid.arrays.after_read state _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
    valuesWord := valid.valuesWord.after_read state _ used values capacity rfl rfl rfl
    reverse := valid.reverse.after_read state _ used orderPos capacity items rfl rfl rfl
    ordered := valid.ordered.after_memory state _ order capacity items rfl
  }

#print axioms HashDeleteLoopInvariantWidth.rank_bounds
#print axioms HashDeleteLoopInvariantWidth.dec_clock
#print axioms hashDeleteStateRank_dec_clock
end InitECandidate.Runtime
