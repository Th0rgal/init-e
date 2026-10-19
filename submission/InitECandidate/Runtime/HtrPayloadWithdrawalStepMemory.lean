import InitECandidate.Runtime.HtrPayloadWithdrawalStepBound
import InitECandidate.Runtime.HtrWithdrawalMemory
import InitECandidate.Runtime.HashRootGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_withdrawal_step_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes array index roots heap watched : BitVec 64) (count : Nat)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (inside : index.toNat < count) (rootsAligned : roots.toNat % 8 = 0)
    (rootsFits : roots.toNat + count * 32 ≤ 33806089496) (rootsBefore : watched.toNat < roots.toNat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrWithdrawalBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadWithdrawalStep = (none,post)) :
    post.memory watched = state.memory watched := by
  unfold htrPayloadWithdrawalStep at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "htr_withdrawal") htrPayloadWithdrawalArguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some stopped => cases run
    | none =>
      dsimp only at run
      have geometry := hashRoot_output_geometry roots index count inside rootsAligned rootsFits
      have frame := htrWithdrawal_call_normal_memory state middle htrPayloadWithdrawalArguments pointer accelerator zeroHashes
        (array + index * (44#64)) heap (roots + index * (32#64)) watched
        (htrPayload_withdrawal_arguments state array index roots arrayLocal indexLocal rootsLocal)
        atPointer atAccel atZero hh geometry.2.1 geometry.2.2
        (Or.inl (by rw [geometry.1]; omega)) heapAligned heapFits heapBefore accelAligned accelFits pointerFits
        accelOutside pointerOutside code budget callRun
      have memory := evaluate_readOnly_memory
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) rfl middle
      rw [run] at memory
      exact (congrFun memory watched).trans frame

#print axioms htrPayload_withdrawal_step_normal_memory
end InitECandidate.Runtime
