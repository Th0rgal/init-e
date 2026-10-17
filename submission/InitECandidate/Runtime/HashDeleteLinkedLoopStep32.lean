import InitECandidate.Runtime.HashDeleteLinkedLoopInvariant32
import InitECandidate.Runtime.HashDeleteLoopStep32
import InitECandidate.Runtime.HashDeleteOccupiedLinkedIteration32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def HashDeleteLinkedLoopExit32 {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state ∧
  ∃ hole, state.locals.lookup (ofString "i") = some (.val (.word hole)) ∧
    HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state

theorem HashDeleteLinkedLoopInvariant32.of_indices {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition hole index : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (base : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (ordered : HashDeleteScanOrder capacity index hole empty) :
    HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state := by
  refine ⟨base,?_⟩
  intro actualHole actualIndex actualHoleLocal actualIndexLocal
  have h : hole = actualHole := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using holeLocal.symm.trans actualHoleLocal
  have i : index = actualIndex := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using indexLocal.symm.trans actualIndexLocal
  subst actualHole
  subst actualIndex
  exact ⟨linked,ordered⟩

theorem HashDeleteLinkedLoopInvariant32.step {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (budget : 34 ≤ state.clock) :
    ∃ post, state.clock ≤ post.clock + 34 ∧ post.clock ≤ state.clock ∧
      ((evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∧
        HashDeleteLinkedLoopExit32 table keys stride capacity used values order orderPos items empty deletedPosition bits post) ∨
       (evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧
        HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
        hashDeleteStateRank capacity empty post < hashDeleteStateRank capacity empty state)) := by
  classical
  obtain ⟨hole,index,holeInside,indexInside,holeLocal,indexLocal,holeOccupied⟩ := valid.base.indices
  obtain ⟨linked,ordered⟩ := valid.linked hole index holeLocal indexLocal
  let next := hashProbeNext index capacity
  have nextInside : next.toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits valid.base.arrays.power indexInside]
    exact Nat.mod_lt _ (by rw [valid.base.arrays.power]; exact Nat.two_pow_pos bits)
  obtain ⟨post,base,cost,remaining,body⟩ := valid.base.step table keys stride capacity used values order orderPos items empty bits state budget
  by_cases emptyNext : hashOccupancyRead state used next = some 0
  · obtain ⟨checked,run,_,_,_,_,_,memory,_,_,domain,endian,_,other⟩ :=
      evaluate_hashDelete_empty_allocated_iteration32 state table keys stride capacity used values order orderPos items index bits
        valid.base.arrays valid.base.valuesWord valid.base.reverse valid.base.ordered indexLocal valid.base.capacityLocal valid.base.usedLocal emptyNext
    have actualRun : evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) := by
      rcases body with stopped | ⟨running,_⟩
      · exact stopped
      · have contradiction := congrArg Prod.fst (running.symm.trans run)
        contradiction
    have same : post = checked := congrArg Prod.snd (actualRun.symm.trans run)
    have postLinked := linked.after_read state checked used order orderPos capacity items hole deletedPosition memory domain endian
    refine ⟨post,cost,remaining,Or.inl ⟨actualRun,base,hole,?_,?_⟩⟩
    · rw [same]; exact (other _ (by decide)).trans holeLocal
    · rw [same]; exact postLinked
  · have different := valid.next_ne_hole table keys stride capacity used values order orderPos items empty deletedPosition hole index bits state holeLocal indexLocal emptyNext
    obtain ⟨checked,run,_,_,_,_,_,_,_,_,_,_,_,scanPost,_,choices,_⟩ :=
      evaluate_hashDelete_occupied_allocated_linked_iteration32 state keys stride hole index values order orderPos used capacity items
        valid.base.keysLocal valid.base.strideLocal holeLocal indexLocal valid.base.sizeLocal valid.base.usedLocal valid.base.capacityLocal
        table bits valid.base.arrays nextInside emptyNext valid.base.keyValueOrder budget valid.base.valuesLocal valid.base.orderLocal valid.base.reverseLocal
        valid.base.reverse valid.base.ordered holeInside valid.base.valuesWord deletedPosition different linked
    have actualRun : evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) := by
      rcases body with stopped | ⟨running,_⟩
      · have contradiction := congrArg Prod.fst (stopped.symm.trans run)
        contradiction
      · exact running
    have same : post = checked := congrArg Prod.snd (actualRun.symm.trans run)
    have notEmpty : next ≠ empty := by intro equal; apply emptyNext; rw [equal]; exact valid.base.emptyRead
    have postValid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits post := by
      rw [same] at base ⊢
      rcases choices with ⟨oldLocal,oldLinked⟩ | ⟨newLocal,newLinked⟩
      · exact HashDeleteLinkedLoopInvariant32.of_indices table keys stride capacity used values order orderPos items empty deletedPosition hole next bits checked base
          oldLocal scanPost oldLinked (ordered.advance capacity index hole empty bits valid.base.arrays.power indexInside valid.base.emptyInside notEmpty)
      · exact HashDeleteLinkedLoopInvariant32.of_indices table keys stride capacity used values order orderPos items empty deletedPosition next next bits checked base
          newLocal scanPost newLinked (HashDeleteScanOrder.initial _ _ _)
    have decrease := hashDeleteRank_decreases capacity index empty bits valid.base.arrays.power indexInside valid.base.emptyInside notEmpty
    refine ⟨post,cost,remaining,Or.inr ⟨actualRun,postValid,?_⟩⟩
    rw [hashDeleteStateRank_of_local capacity empty index state indexLocal,same,
      hashDeleteStateRank_of_local capacity empty next checked scanPost]
    exact decrease

#print axioms HashDeleteLinkedLoopInvariant32.of_indices
#print axioms HashDeleteLinkedLoopInvariant32.step
end InitECandidate.Runtime
