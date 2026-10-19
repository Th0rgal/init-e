import InitECandidate.Runtime.HtrPayloadWithdrawalLoopBound
import InitECandidate.Runtime.HtrPayloadWithdrawalStepMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrPayloadWithdrawalMemoryState (pointer accelerator zeroHashes array roots heap count watched : BitVec 64)
    (word : HolWordLab 64) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat)
    extends HtrPayloadWithdrawalState array roots heap count state rank : Prop where
  pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer))
  accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  cell : state.memory watched = word

theorem htrPayload_withdrawal_loop_memory_ranked (pointer accelerator zeroHashes array roots heap count watched : BitVec 64)
    (word : HolWordLab 64) (countBound : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      HtrPayloadWithdrawalMemoryState pointer accelerator zeroHashes array roots heap count watched word state rank →
      rank * (htrWithdrawalBodyCost + 2) ≤ state.clock →
      RankedOutcome state htrPayloadWithdrawalCondition (rank * (htrWithdrawalBodyCost + 2))
        (HtrPayloadWithdrawalMemoryState pointer accelerator zeroHashes array roots heap count watched word) False
        (evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep)) := by
  refine rankedWhile_run htrPayloadWithdrawalCondition htrPayloadWithdrawalStep (htrWithdrawalBodyCost + 1)
    (HtrPayloadWithdrawalMemoryState pointer accelerator zeroHashes array roots heap count watched word) False ?_ ?_
  · intro F state valid flag guard
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "nwd") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalCondition = _ at condition
    rw [condition] at guard
    have stopped : ¬ index.toNat < count.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank flag code valid guard nonzero budget
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "nwd") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalCondition = _ at condition
    have running : index.toNat < count.toNat := by
      by_contra stopped
      rw [condition] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : htrWithdrawalBodyCost + 1 ≤ (decClockHOLFinite state).clock := by
      change htrWithdrawalBodyCost + 1 ≤ state.clock - 1
      omega
    have bounded := runBounded_htrPayload_withdrawal_step (decClockHOLFinite state) array index roots heap
      valid.arrayLocal atIndex valid.rootsLocal valid.heapGlobal heapFits code enough
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) htrPayloadWithdrawalStep with
        | mk result post =>
          rw [bodyRun] at normal
          dsimp only at normal
          subst normal
          have facts := htrPayload_withdrawal_step_normal (decClockHOLFinite state) post array index roots heap
            valid.arrayLocal atIndex valid.rootsLocal valid.heapGlobal code bodyRun
          have frame := htrPayload_withdrawal_step_normal_memory (decClockHOLFinite state) post
            pointer accelerator zeroHashes array index roots heap watched count.toNat
            valid.arrayLocal atIndex valid.rootsLocal running rootsAligned rootsFits rootsBefore
            valid.pointerGlobal valid.accelGlobal valid.zeroGlobal valid.heapGlobal
            heapAligned heapFits heapBefore accelAligned accelFits pointerFits accelOutside pointerOutside code enough bodyRun
          have natural : (index + (1#64)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
            rfl
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) htrPayloadWithdrawalStep
          rw [bodyRun] at metadata
          refine ⟨count.toNat - (index + (1#64)).toNat,by rw [natural]; omega,?_,metadata.1⟩
          exact {
            pointerGlobal := by rw [facts.1]; exact valid.pointerGlobal
            accelGlobal := by rw [facts.1]; exact valid.accelGlobal
            zeroGlobal := by rw [facts.1]; exact valid.zeroGlobal
            cell := frame.trans valid.cell
            heapGlobal := by rw [facts.1]; exact valid.heapGlobal
            arrayLocal := (facts.2.2 _ (by decide)).trans valid.arrayLocal
            rootsLocal := (facts.2.2 _ (by decide)).trans valid.rootsLocal
            countLocal := (facts.2.2 _ (by decide)).trans valid.countLocal
            cursor := ⟨index + (1#64),facts.2.1,by rw [natural]; omega,Nat.le_refl _⟩ }
      · exact absurd cont (evaluate_noTopContinue htrPayloadWithdrawalStep (by decide) (decClockHOLFinite state))
    · intro broken
      exact absurd broken (evaluate_noTopBreak htrPayloadWithdrawalStep (by decide) (decClockHOLFinite state))



theorem htrPayload_withdrawal_loop_normal_memory (pointer accelerator zeroHashes array roots heap count watched : BitVec 64)
    (countBound : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (budget : rank * (htrWithdrawalBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) = (none,post)) :
    post.memory watched = state.memory watched := by
  have initial : HtrPayloadWithdrawalMemoryState pointer accelerator zeroHashes array roots heap count watched
      (state.memory watched) state rank :=
    { toHtrPayloadWithdrawalState := valid, pointerGlobal := pointerGlobal, accelGlobal := accelGlobal,
      zeroGlobal := zeroGlobal, cell := rfl }
  have loop := htrPayload_withdrawal_loop_memory_ranked pointer accelerator zeroHashes array roots heap count watched
    (state.memory watched) countBound rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore
    accelAligned accelFits pointerFits accelOutside pointerOutside rank state code initial budget
  rw [run] at loop
  obtain ⟨nextRank,next,_,_⟩ := loop.2.2.2 rfl
  exact next.cell

#print axioms htrPayload_withdrawal_loop_normal_memory
#print axioms htrPayload_withdrawal_loop_memory_ranked
end InitECandidate.Runtime
