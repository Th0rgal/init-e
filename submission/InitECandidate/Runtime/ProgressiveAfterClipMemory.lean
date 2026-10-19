import InitECandidate.Runtime.ProgressiveStepReturned
import InitECandidate.Runtime.ProgressivePowerCounters
import InitECandidate.Runtime.MerkleizeMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real clipped progressive iteration hashes into its allocated root
slot and then performs only local counter updates. -/
theorem progressiveAfterClip_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p off cnt size roots k heap watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hc : state.locals.lookup (ofString "cnt") = some (.val (.word cnt)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : cnt.toNat ≤ 134217712) (index : k.toNat < 24)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 768 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : merkleBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state progressiveAfterClip = (none,post)) :
    post.memory watched = state.memory watched := by
  have geometry := progressive_root_output_geometry roots k index rootsAligned rootsFits
  rw [source_progressive_after_clip,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize") progressiveMerkleArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some stopped => cases run
    | none =>
      have frame := merkleize_call_normal_memory state middle progressiveMerkleArguments pointer accelerator heap zeroHashes size
        (roots + k * (32#64)) cnt (p + off * (32#64)) watched
        (progressive_arguments state p off cnt size roots k hp ho hc hs hr hk) atPointer atAccel atZero hh heapFits
        small geometry.2.1 geometry.2.2 (Or.inl (by rw [geometry.1]; omega)) heapAligned heapBefore accelAligned accelFits
        pointerFits accelOutside pointerOutside code budget called
      dsimp only at run
      have memory := evaluate_readOnly_memory progressiveUpdates (by rw [source_progressive_updates]; rfl) middle
      rw [run] at memory
      exact (congrFun memory watched).trans frame

#print axioms progressiveAfterClip_normal_memory
end InitECandidate.Runtime
