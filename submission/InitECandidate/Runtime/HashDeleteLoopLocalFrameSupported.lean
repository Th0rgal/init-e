import InitECandidate.Runtime.HashDeleteLoopStepSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both actual body branches preserve locals outside the scan's working set. -/
theorem HashDeleteLoopInvariantWidth.body_local_frame_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state post : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : 54 ≤ state.clock)
    (run : ∃ result, evaluateHOLFiniteState state hashDeleteLoopBody = (result,post))
    (name : MlS) (notHole : name ≠ ofString "i") (notScan : name ≠ ofString "j")
    (notHash : name ≠ ofString "h") (notHome : name ≠ ofString "home") (notMovable : name ≠ ofString "movable") :
    post.locals.lookup name = state.locals.lookup name := by
  classical
  have width : keyLength.toNat ≤ 52 := by
    rcases supported with rfl | rfl | rfl <;> decide
  obtain ⟨hole,index,holeInside,indexInside,holeLocal,indexLocal,_⟩ := valid.indices
  obtain ⟨result,actual⟩ := run
  let next := hashProbeNext index capacity
  have nextInside : next.toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits valid.arrays.power indexInside]
    exact Nat.mod_lt _ (by rw [valid.arrays.power]; exact Nat.two_pow_pos bits)
  by_cases emptyNext : hashOccupancyRead state used next = some 0
  · obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,_,_,_,_,other⟩ :=
      evaluate_hashDelete_empty_allocated_iteration_width state keyLength table keys stride capacity used values order orderPos items index bits
        valid.arrays valid.valuesWord valid.reverse valid.ordered indexLocal valid.capacityLocal valid.usedLocal emptyNext
    have same : post = checked := congrArg Prod.snd (actual.symm.trans checkedRun)
    rw [same]
    exact other name notScan
  · obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,_,_,_,_,_,_,other⟩ :=
      evaluate_hashDelete_occupied_allocated_iteration_supported state keyLength keys stride hole index values order orderPos used capacity items
        valid.keysLocal valid.strideLocal holeLocal indexLocal valid.sizeLocal valid.usedLocal valid.capacityLocal
        table bits supported valid.arrays nextInside emptyNext valid.keyValueOrder (by omega) valid.valuesLocal valid.orderLocal valid.reverseLocal
        valid.reverse valid.ordered holeInside valid.valuesWord
    have same : post = checked := congrArg Prod.snd (actual.symm.trans checkedRun)
    rw [same]
    exact other name notHole notScan notHash notHome notMovable

#print axioms HashDeleteLoopInvariantWidth.body_local_frame_supported
end InitECandidate.Runtime
