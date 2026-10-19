import InitECandidate.Runtime.ProgressiveLoopMemory
import InitECandidate.Runtime.ProgressiveZeroMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveLoops_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n off size roots k heap acc out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat)
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712) (counters : ProgressivePowerCounters n off size k)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 768 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : (n.toNat - off.toNat) * (merkleBodyCost + 2) + (16 + (progressiveFoldCost + 16)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (progressiveAt 6) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have loopBudget : (n.toNat - off.toNat) * (merkleBodyCost + 2) ≤ state.clock :=
    (Nat.le_add_right _ _).trans budget
  rw [source_progressive_loop] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile (.while progressiveCondition progressiveStep) (by decide) state v) run
  obtain ⟨frame,globals,finalK,atFinalK,finalKBound⟩ := progressiveLoop_normal_frame state middle
    pointer accelerator zeroHashes p n off size roots k heap watched
    atPointer atAccel atZero hp ho hn hs hr hk hh small counters rootsAligned rootsFits rootsBefore
    heapAligned heapFits heapBefore accelAligned accelFits pointerFits accelOutside pointerOutside code loopBudget normal
  have clocks := runBounded_progressive_loop state p n roots heap (n.toNat - off.toNat) small heapFits code
    ⟨hp,hn,hr,hh,off,size,k,ho,hs,hk,counters.1,Nat.le_refl _⟩ loopBudget
  have meta' := evaluateHOLFiniteState_metadata state (.while progressiveCondition progressiveStep)
  unfold RunBounded at clocks
  rw [normal] at clocks meta'
  have keep (key : MlS) (supported : avoidsLocal key (.while progressiveCondition progressiveStep) = true) :
      middle.locals.lookup key = state.locals.lookup key :=
      by
    have kept := evaluate_avoidsLocal_flowing key (.while progressiveCondition progressiveStep) supported state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept
  have tailBudget : 16 + (progressiveFoldCost + 16) ≤ middle.clock := by
    have credit := clocks.1
    exact Nat.le_of_add_le_add_right
      ((show (16 + (progressiveFoldCost + 16)) + (n.toNat - off.toNat) * (merkleBodyCost + 2) ≤ state.clock from
        by simpa only [Nat.add_comm] using budget).trans credit)
  have suffix := progressiveZero_suffix_returned_memory middle post pointer accelerator roots acc finalK out mark watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel)
    ((keep _ (by decide)).trans hr) ((keep _ (by decide)).trans atAcc) atFinalK
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside (finalKBound.trans (Nat.mul_le_mul_left 4 small))
    accAligned accFits accBefore accelAligned accelFits pointerFits accelOutside pointerOutside
    (meta'.1.trans code) tailBudget tail
  exact suffix.trans frame

#print axioms progressiveLoops_returned_memory
end InitECandidate.Runtime
