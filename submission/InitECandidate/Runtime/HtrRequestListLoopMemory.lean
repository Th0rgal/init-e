import InitECandidate.Runtime.HtrRequestListLoopBound
import InitECandidate.Runtime.HtrRequestListStepMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrRequestListMemoryState (sha accelerator zeroHashes kind pointer size roots heap count watched : BitVec 64)
    (word : HolWordLab 64) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat)
    extends HtrRequestListState kind pointer size roots heap count state rank : Prop where
  pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word sha))
  accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  cell : state.memory watched = word

theorem htrRequestList_loop_memory_ranked (sha accelerator zeroHashes kind pointer size roots heap count watched : BitVec 64)
    (word : HolWordLab 64) (countBound : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : sha.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < sha.toNat ∨ sha.toNat + 64 ≤ watched.toNat) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      HtrRequestListMemoryState sha accelerator zeroHashes kind pointer size roots heap count watched word state rank →
      rank * (htrRequestStepCost + 1) ≤ state.clock →
      RankedOutcome state htrRequestListCondition (rank * (htrRequestStepCost + 1))
        (HtrRequestListMemoryState sha accelerator zeroHashes kind pointer size roots heap count watched word) False
        (evaluateHOLFiniteState state (.while htrRequestListCondition htrRequestListStep)) := by
  refine rankedWhile_run htrRequestListCondition htrRequestListStep (htrRequestStepCost)
    (HtrRequestListMemoryState sha accelerator zeroHashes kind pointer size roots heap count watched word) False ?_ ?_
  · intro F state valid flag guard
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "n") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrRequestListCondition = _ at condition
    rw [condition] at guard
    have stopped : ¬ index.toNat < count.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank flag code valid guard nonzero budget
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "n") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrRequestListCondition = _ at condition
    have running : index.toNat < count.toNat := by
      by_contra stopped
      rw [condition] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : htrRequestStepCost ≤ (decClockHOLFinite state).clock := by
      change htrRequestStepCost ≤ state.clock - 1
      omega
    have bounded := htrRequestList_step_bound (decClockHOLFinite state) kind pointer index size roots heap
      ⟨valid.kindLocal,valid.pointerLocal,atIndex,valid.sizeLocal,valid.rootsLocal⟩ valid.heapGlobal heapFits code enough
    refine ⟨bounded.1.1,bounded.1.2.1,bounded.1.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) htrRequestListStep with
        | mk result post =>
          rw [bodyRun] at normal
          dsimp only at normal
          subst normal
          have facts := bounded.2 post bodyRun
          have outputNat : (roots + index * (32#64)).toNat = roots.toNat + index.toNat * 32 := by
            apply word_mul_add_toNat
            change roots.toNat + index.toNat * 32 < 2 ^ 64
            omega
          have outputAligned : (roots + index * (32#64)).toNat % 8 = 0 := by
            rw [outputNat,Nat.add_mod,rootsAligned,Nat.mul_mod]
            simp
          have layout : HashMemoryLayout (decClockHOLFinite state) sha accelerator zeroHashes heap
              (roots + index * (32#64)) watched := {
            atSha := valid.pointerGlobal
            atAccel := valid.accelGlobal
            atZero := valid.zeroGlobal
            atHeap := valid.heapGlobal
            outAligned := outputAligned
            outFits := by rw [outputNat]; omega
            outOutside := Or.inl (by rw [outputNat]; omega)
            heapAligned := heapAligned
            heapFits := heapFits
            heapBefore := heapBefore
            accelAligned := accelAligned
            accelFits := accelFits
            shaFits := pointerFits
            accelOutside := accelOutside
            shaOutside := pointerOutside
            code := code }
          have frame := htrRequestList_step_normal_frame (decClockHOLFinite state) post kind pointer index size roots heap
            sha accelerator zeroHashes watched ⟨valid.kindLocal,valid.pointerLocal,atIndex,valid.sizeLocal,valid.rootsLocal⟩
            layout enough bodyRun
          have natural : (index + (1#64)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
            rfl
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) htrRequestListStep
          rw [bodyRun] at metadata
          refine ⟨count.toNat - (index + (1#64)).toNat,by rw [natural]; omega,?_,metadata.1⟩
          exact {
            pointerGlobal := by rw [frame.2]; exact valid.pointerGlobal
            accelGlobal := by rw [frame.2]; exact valid.accelGlobal
            zeroGlobal := by rw [frame.2]; exact valid.zeroGlobal
            cell := frame.1.trans valid.cell
            heapGlobal := facts.1
            pointerLocal := (facts.2.2 _ (by decide)).trans valid.pointerLocal
            kindLocal := (facts.2.2 _ (by decide)).trans valid.kindLocal
            sizeLocal := (facts.2.2 _ (by decide)).trans valid.sizeLocal
            rootsLocal := (facts.2.2 _ (by decide)).trans valid.rootsLocal
            countLocal := (facts.2.2 _ (by decide)).trans valid.countLocal
            cursor := ⟨index + (1#64),facts.2.1,by rw [natural]; omega,Nat.le_refl _⟩ }
      · exact absurd cont (evaluate_noTopContinue htrRequestListStep (by decide) (decClockHOLFinite state))
    · intro broken
      exact absurd broken (evaluate_noTopBreak htrRequestListStep (by decide) (decClockHOLFinite state))



theorem htrRequestList_loop_normal_memory (sha accelerator zeroHashes kind pointer size roots heap count watched : BitVec 64)
    (countBound : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : sha.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < sha.toNat ∨ sha.toNat + 64 ≤ watched.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrRequestListState kind pointer size roots heap count state rank)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word sha)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (budget : rank * (htrRequestStepCost + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrRequestListCondition htrRequestListStep) = (none,post)) :
    post.memory watched = state.memory watched := by
  have initial : HtrRequestListMemoryState sha accelerator zeroHashes kind pointer size roots heap count watched
      (state.memory watched) state rank :=
    { toHtrRequestListState := valid, pointerGlobal := pointerGlobal, accelGlobal := accelGlobal,
      zeroGlobal := zeroGlobal, cell := rfl }
  have loop := htrRequestList_loop_memory_ranked sha accelerator zeroHashes kind pointer size roots heap count watched
    (state.memory watched) countBound rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore
    accelAligned accelFits pointerFits accelOutside pointerOutside rank state code initial budget
  rw [run] at loop
  obtain ⟨nextRank,next,_,_⟩ := loop.2.2.2 rfl
  exact next.cell

#print axioms htrRequestList_loop_normal_memory
#print axioms htrRequestList_loop_memory_ranked
end InitECandidate.Runtime
