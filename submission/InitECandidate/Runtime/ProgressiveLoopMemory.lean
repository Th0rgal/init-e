import InitECandidate.Runtime.ProgressiveStepMemory
import InitECandidate.Runtime.ProgressiveStepGlobals
import InitECandidate.Runtime.ProgressiveStepReturned
import InitECandidate.Runtime.ProgressiveLoopBound
import InitECandidate.Runtime.NormalWhileInvariantByGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveLoop_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n off size roots k heap watched : BitVec 64)
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
    (small : n.toNat ≤ 134217712) (counters : ProgressivePowerCounters n off size k)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 768 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : (n.toNat - off.toNat) * (merkleBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while progressiveCondition progressiveStep) = (none,post)) :
    post.memory watched = state.memory watched ∧ post.globals = state.globals ∧
      ∃ finalK : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word finalK)) ∧
        finalK.toNat ≤ 4 * n.toNat := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧ current.globals = state.globals ∧
    current.locals.lookup (ofString "p") = some (.val (.word p)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word n)) ∧
    current.locals.lookup (ofString "roots") = some (.val (.word roots)) ∧
    current.code = originalRuntimeCode ∧
    ∃ off size k : BitVec 64,
      current.locals.lookup (ofString "off") = some (.val (.word off)) ∧
      current.locals.lookup (ofString "size") = some (.val (.word size)) ∧
      current.locals.lookup (ofString "k") = some (.val (.word k)) ∧
      ProgressivePowerCounters n off size k ∧
      (n.toNat - off.toNat) * (merkleBodyCost + 2) ≤ current.clock
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ _ Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,globals,pLocal,nLocal,rootsLocal,installed,off,size,k,offLocal,sizeLocal,kLocal,valid,remaining⟩ := invariant
    have running : off.toNat < n.toNat := by
      by_contra stopped
      rw [eval_progressive_condition current off n offLocal nLocal] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : merkleBodyCost + 1 ≤ (decClockHOLFinite current).clock := by
      change merkleBodyCost + 1 ≤ current.clock - 1
      have positive : 1 ≤ n.toNat - off.toNat := by omega
      have lower := Nat.mul_le_mul_right (merkleBodyCost + 2) positive
      omega
    have frame := progressiveStep_normal_memory (decClockHOLFinite current) next
      pointer accelerator zeroHashes p n off size roots k heap watched
      (by change current.globals.lookup _ = _; rw [globals]; exact atPointer)
      (by change current.globals.lookup _ = _; rw [globals]; exact atAccel)
      (by change current.globals.lookup _ = _; rw [globals]; exact atZero)
      pLocal offLocal nLocal sizeLocal rootsLocal kLocal
      (by change current.globals.lookup _ = _; rw [globals]; exact hh)
      small valid running rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore
      accelAligned accelFits pointerFits accelOutside pointerOutside installed enough bodyRun
    have globalFrame := progressiveStep_normal_globals (decClockHOLFinite current) next
      p n off size roots k heap pLocal nLocal offLocal sizeLocal rootsLocal kLocal
      (by change current.globals.lookup _ = _; rw [globals]; exact hh) installed bodyRun
    have locals := (progressive_step_normal (decClockHOLFinite current) next
      p n off size roots k heap pLocal nLocal offLocal sizeLocal rootsLocal kLocal
      (by change current.globals.lookup _ = _; rw [globals]; exact hh) installed bodyRun).2
    have kept (key : MlS) (different : key ≠ ofString "cnt") := locals key different
    have nextP : next.locals.lookup (ofString "p") = some (.val (.word p)) := by
      rw [kept _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact pLocal
    have nextN : next.locals.lookup (ofString "n") = some (.val (.word n)) := by
      rw [kept _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact nLocal
    have nextRoots : next.locals.lookup (ofString "roots") = some (.val (.word roots)) := by
      rw [kept _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact rootsLocal
    have nextOff : next.locals.lookup (ofString "off") = some (.val (.word (off + size))) := by
      rw [kept _ (by decide)]; exact (progressive_update_fields (decClockHOLFinite current) off size k).1
    have nextSize : next.locals.lookup (ofString "size") = some (.val (.word (size <<< (2 : Nat)))) := by
      rw [kept _ (by decide)]; exact (progressive_update_fields (decClockHOLFinite current) off size k).2.1
    have nextK : next.locals.lookup (ofString "k") = some (.val (.word (k + (1#64)))) := by
      rw [kept _ (by decide)]; exact (progressive_update_fields (decClockHOLFinite current) off size k).2.2
    have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite current) progressiveStep
    have spent := (runBounded_progressive_step (decClockHOLFinite current) p n off size roots k heap
      pLocal nLocal offLocal sizeLocal rootsLocal kLocal small (Nat.le_of_lt running)
      (by change current.globals.lookup _ = _; rw [globals]; exact hh) heapFits installed enough).1
    rw [bodyRun] at metadata spent
    refine ⟨frame.trans memory,globalFrame.trans globals,nextP,nextN,nextRoots,metadata.1.trans installed,
      off + size,size <<< (2 : Nat),k + (1#64),nextOff,nextSize,nextK,
      progressive_power_counters_step n off size k small valid running,?_⟩
    have decreased := (progressive_counters_step n off size k small valid.1 running).2.2.2.2
    have rankLe : n.toNat - (off + size).toNat + 1 ≤ n.toNat - off.toNat := by omega
    have scaled := Nat.mul_le_mul_right (merkleBodyCost + 2) rankLe
    change current.clock - 1 ≤ next.clock + (merkleBodyCost + 1) at spent
    rw [Nat.add_mul] at scaled
    omega)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,rfl,hp,hn,hr,code,off,size,k,ho,hs,hk,counters,budget⟩ run
  obtain ⟨memory,globals,_,_,_,_,finalOff,finalSize,finalK,_,_,atFinalK,valid,_⟩ := finalInvariant
  exact ⟨memory,globals,finalK,atFinalK,Nat.le_trans valid.1.2.2 valid.1.1⟩

#print axioms progressiveLoop_normal_frame
end InitECandidate.Runtime
