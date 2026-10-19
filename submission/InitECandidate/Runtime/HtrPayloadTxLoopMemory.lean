import InitECandidate.Runtime.HtrPayloadTxLoopBound
import InitECandidate.Runtime.HtrPayloadTxStepMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrPayloadTxMemoryState (pointer accelerator zeroHashes chunk array roots heap input inputLength count watched : BitVec 64)
    (word : HolWordLab 64) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat)
    extends HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank : Prop where
  cell : state.memory watched = word

theorem htrPayload_tx_loop_memory_ranked (pointer accelerator zeroHashes chunk array roots heap input inputLength count watched : BitVec 64) (word : HolWordLab 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (rootsBefore : watched.toNat < roots.toNat) (heapBefore : watched.toNat < heap.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      HtrPayloadTxMemoryState pointer accelerator zeroHashes chunk array roots heap input inputLength count watched word state rank →
      rank * (htrPbytesBodyCost + 2) ≤ state.clock →
      RankedOutcome state htrPayloadTxCondition (rank * (htrPbytesBodyCost + 2))
        (HtrPayloadTxMemoryState pointer accelerator zeroHashes chunk array roots heap input inputLength count watched word) False
        (evaluateHOLFiniteState state (.while htrPayloadTxCondition htrPayloadTxStep)) := by
  refine rankedWhile_run htrPayloadTxCondition htrPayloadTxStep (htrPbytesBodyCost + 1)
    (HtrPayloadTxMemoryState pointer accelerator zeroHashes chunk array roots heap input inputLength count watched word) False ?_ ?_
  · intro F state valid flag guard
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "ntx") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadTxCondition = _ at condition
    rw [condition] at guard
    have stopped : ¬ index.toNat < count.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank flag code valid guard nonzero budget
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "ntx") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadTxCondition = _ at condition
    have running : index.toNat < count.toNat := by
      by_contra stopped
      rw [condition] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    obtain ⟨p,n,entry⟩ := valid.slices index running
    have lengthBound := (entry.length_bound state array index p n input inputLength).trans small
    have enough : htrPbytesBodyCost + 1 ≤ (decClockHOLFinite state).clock := by
      change htrPbytesBodyCost + 1 ≤ state.clock - 1
      omega
    have clockEntry : RlpSliceEntry (decClockHOLFinite state) array index p n :=
      entry.readable.after_frame state (decClockHOLFinite state) array index p n rfl rfl rfl
    have clockSlices : RlpSliceInputPrefix (decClockHOLFinite state) array input inputLength count.toNat := by
      intro slot inside
      obtain ⟨p,n,old⟩ := valid.slices slot inside
      exact ⟨p,n,old.after_frame state (decClockHOLFinite state) array slot p n input inputLength rfl rfl rfl⟩
    have bounded := runBounded_htrPayload_tx_step (decClockHOLFinite state) array index p n roots heap
      valid.arrayLocal atIndex valid.rootsLocal clockEntry lengthBound valid.heapGlobal heapFits code enough
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) htrPayloadTxStep with
        | mk result post =>
          rw [bodyRun] at normal
          dsimp only at normal
          subst normal
          have facts := htrPayload_tx_step_normal (decClockHOLFinite state) post array index p n roots heap
            valid.arrayLocal atIndex valid.rootsLocal clockEntry valid.heapGlobal code bodyRun
          have slices := htrPayload_tx_step_preserves_slices (decClockHOLFinite state) post pointer accelerator zeroHashes chunk
            array index roots heap input inputLength count.toNat valid.arrayLocal atIndex valid.rootsLocal clockSlices
            running small arrayRoots arrayHeap rootsAligned rootsFits valid.pointerGlobal valid.accelGlobal valid.chunkGlobal
            chunkAligned chunkFits valid.zeroGlobal valid.heapGlobal heapAligned heapFits accelAligned accelFits pointerFits code enough bodyRun
          have frame := htrPayload_tx_step_normal_memory (decClockHOLFinite state) post
            pointer accelerator zeroHashes chunk array index p n roots heap watched count.toNat
            valid.arrayLocal atIndex valid.rootsLocal clockEntry running rootsAligned rootsFits rootsBefore
            valid.pointerGlobal valid.accelGlobal valid.chunkGlobal chunkAligned (by omega) chunkOutside
            valid.zeroGlobal valid.heapGlobal lengthBound heapAligned heapFits heapBefore accelAligned
            (by omega) (by omega) accelOutside pointerOutside code enough bodyRun
          have natural : (index + (1#64)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
            rfl
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) htrPayloadTxStep
          rw [bodyRun] at metadata
          refine ⟨count.toNat - (index + (1#64)).toNat,by rw [natural]; omega,?_,metadata.1⟩
          exact {
            cell := frame.trans valid.cell
            pointerGlobal := by rw [facts.1]; exact valid.pointerGlobal
            accelGlobal := by rw [facts.1]; exact valid.accelGlobal
            zeroGlobal := by rw [facts.1]; exact valid.zeroGlobal
            chunkGlobal := by rw [facts.1]; exact valid.chunkGlobal
            heapGlobal := by rw [facts.1]; exact valid.heapGlobal
            arrayLocal := (facts.2.2 _ (by decide)).trans valid.arrayLocal
            rootsLocal := (facts.2.2 _ (by decide)).trans valid.rootsLocal
            countLocal := (facts.2.2 _ (by decide)).trans valid.countLocal
            slices := slices
            cursor := ⟨index + (1#64),facts.2.1,by rw [natural]; omega,Nat.le_refl _⟩ }
      · exact absurd cont (evaluate_noTopContinue htrPayloadTxStep (by decide) (decClockHOLFinite state))
    · intro broken
      exact absurd broken (evaluate_noTopBreak htrPayloadTxStep (by decide) (decClockHOLFinite state))


theorem htrPayload_tx_loop_normal_memory (pointer accelerator zeroHashes chunk array roots heap input inputLength count watched : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (rootsBefore : watched.toNat < roots.toNat) (heapBefore : watched.toNat < heap.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (budget : rank * (htrPbytesBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrPayloadTxCondition htrPayloadTxStep) = (none,post)) :
    post.memory watched = state.memory watched := by
  have initial : HtrPayloadTxMemoryState pointer accelerator zeroHashes chunk array roots heap input inputLength count watched
      (state.memory watched) state rank := { toHtrPayloadTxState := valid, cell := rfl }
  have loop := htrPayload_tx_loop_memory_ranked pointer accelerator zeroHashes chunk array roots heap input inputLength count watched
    (state.memory watched) small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits rootsBefore heapBefore chunkOutside accelOutside pointerOutside rank state code initial budget
  rw [run] at loop
  obtain ⟨nextRank,next,_,_⟩ := loop.2.2.2 rfl
  exact next.cell

#print axioms htrPayload_tx_loop_normal_memory
#print axioms htrPayload_tx_loop_memory_ranked
end InitECandidate.Runtime
