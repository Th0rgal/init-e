import InitECandidate.Runtime.HtrPayloadTxLoopGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_loop_normal_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (budget : rank * (htrPbytesBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrPayloadTxCondition htrPayloadTxStep) = (none,post)) :
    HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count post 0 ∧
      post.locals.lookup (ofString "i") = some (.val (.word count)) ∧
      post.code = originalRuntimeCode := by
  have loop := htrPayload_tx_loop_ranked_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits rank state code valid budget
  rw [run] at loop
  obtain ⟨nextRank,next,nextCode,stopped⟩ := loop.2.2.2 rfl
  have zero := stopped.resolve_right id
  obtain ⟨index,atIndex,within,_⟩ := next.cursor
  have condition := eval_localBound_less post (ofString "i") (ofString "ntx") .less (Or.inl rfl)
    index count (by omega) (by omega) atIndex next.countLocal
  change evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) htrPayloadTxCondition = _ at condition
  have finished : index.toNat = count.toNat := by
    by_contra different
    have running : index.toNat < count.toNat := by omega
    rw [condition] at zero
    simp [running] at zero
  have equal : index = count := BitVec.eq_of_toNat_eq finished
  subst index
  exact ⟨{ next with cursor := ⟨count,atIndex,Nat.le_refl _,by simp⟩ },atIndex,nextCode.trans code⟩

#print axioms htrPayload_tx_loop_normal_guarded
end InitECandidate.Runtime
