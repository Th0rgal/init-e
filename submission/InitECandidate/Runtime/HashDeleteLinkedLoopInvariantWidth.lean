import InitECandidate.Runtime.HashDeleteLoopInvariantWidth
import InitECandidate.Runtime.HashDeleteOrderLinkedRead
import InitECandidate.Runtime.HashDeleteScanOrder
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Before a deletion loop body, the actual hole has coherent order links and
lies behind the actual scan index relative to the fixed empty witness. -/
structure HashDeleteLinkedLoopInvariantWidth {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  base : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state
  linked : ∀ hole index : BitVec 64,
    state.locals.lookup (ofString "i") = some (.val (.word hole)) →
    state.locals.lookup (ofString "j") = some (.val (.word index)) →
    HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state ∧
    HashDeleteScanOrder capacity index hole empty

theorem HashDeleteLinkedLoopInvariantWidth.dec_clock {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state) :
    HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits (decClockHOLFinite state) := by
  refine ⟨valid.base.dec_clock keyLength table keys stride capacity used values order orderPos items empty bits state,?_⟩
  intro hole index holeLocal indexLocal
  obtain ⟨linked,ordered⟩ := valid.linked hole index holeLocal indexLocal
  exact ⟨linked.after_read state _ used order orderPos capacity items hole deletedPosition rfl rfl rfl,ordered⟩

/-- The separation premise needed by occupied movement follows from the loop invariant. -/
theorem HashDeleteLinkedLoopInvariantWidth.next_ne_hole {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition hole index : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (occupied : hashOccupancyRead state used (hashProbeNext index capacity) ≠ some 0) :
    hashProbeNext index capacity ≠ hole := by
  obtain ⟨actualHole,actualIndex,_,inside,_,binding,_⟩ := valid.base.indices
  have same : actualIndex = index := by
    have words := binding.symm.trans indexLocal
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using words
  have notEmpty : hashProbeNext index capacity ≠ empty := by
    intro equal
    apply occupied
    rw [equal]
    exact valid.base.emptyRead
  exact (valid.linked hole index holeLocal indexLocal).2.next_ne_hole capacity index hole empty bits
    valid.base.arrays.power (by simpa [same] using inside) valid.base.emptyInside notEmpty

#print axioms HashDeleteLinkedLoopInvariantWidth.dec_clock
#print axioms HashDeleteLinkedLoopInvariantWidth.next_ne_hole
end InitECandidate.Runtime
