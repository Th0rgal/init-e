import InitECandidate.Runtime.OriginalBn254InitCode
import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.StoreFourWords
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def bnP : List (BitVec 64) := [4332616871279656263,10917124144477883021,13281191951274694749,3486998266802970665]

def bnAccelTail3 : ProgHOL 64 :=
    .seq (.assign .global (ofString "bn_accel_g1_p1") (.var .global (ofString "bn_accel_g1_params")))
    (.seq (.assign .global (ofString "bn_accel_g1_p2") (.op .add [.var .global (ofString "bn_accel_g1_params"),.const 64]))
    (.return (.const 0)))

def bnAccelTail2 : ProgHOL 64 :=
    .seq (.assign .global (ofString "bn_accel_fp2_f1") (.var .global (ofString "bn_accel_fp2_params")))
    (.seq (.assign .global (ofString "bn_accel_fp2_f2") (.op .add [.var .global (ofString "bn_accel_fp2_params"),.const 64]))
    (globalAllocationProgram [(ofString "bn_accel_g1_params",128)] bnAccelTail3))

def bnAccelTail1 : ProgHOL 64 :=
    .seq (.assign .global (ofString "bn_accel_a") (.var .global (ofString "bn_accel_params")))
    (.seq (.assign .global (ofString "bn_accel_b") (.op .add [.var .global (ofString "bn_accel_params"),.const 32]))
    (.seq (.assign .global (ofString "bn_accel_zero") (.op .add [.var .global (ofString "bn_accel_params"),.const 64]))
    (.seq (.assign .global (ofString "bn_accel_m") (.op .add [.var .global (ofString "bn_accel_params"),.const 96]))
    (.seq (.assign .global (ofString "bn_accel_d") (.op .add [.var .global (ofString "bn_accel_params"),.const 128]))
    (.seq (.store (.var .global (ofString "bn_accel_zero")) (.rstruct [.const 0,.const 0,.const 0,.const 0]))
    (.seq (.store (.var .global (ofString "bn_accel_m"))
        (.rstruct [.const 4332616871279656263,.const 10917124144477883021,.const 13281191951274694749,.const 3486998266802970665]))
    (globalAllocationProgram [(ofString "bn_accel_fp2_params",128)] bnAccelTail2)))))))

theorem source_bn254AccelInit_body : sourceFunctionBody Guest.guestFn_bn254_accel_init =
    .seq (.ite (.cmp .notEqual (.var .global (ofString "bn_accel_params")) (.const 0)) (.return (.const 0)) .skip)
    (globalAllocationProgram [(ofString "bn_accel_params",160)] bnAccelTail1) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_bn254AccelInit_body

/-- Assigning a word-valued expression to an existing word global. -/
theorem evaluate_assign_global_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (source : ExpHOL 64) (old value : BitVec 64)
    (present : state.globals.lookup name = some (.val (.word old)))
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) source = some (.val (.word value))) :
    evaluateHOLFiniteState state (.assign .global name source) =
      (none,setGlobalHOLFinite name (.val (.word value)) state) := by
  simp [evaluateHOLFiniteState_assign,evaluated,isValidValueHOLExact,
    lookupKvarHOLExact,present,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

#print axioms evaluate_assign_global_word

/-- An aligned allocation of a multiple of eight bytes ends exactly at pointer + size. -/
theorem allocationEnd_aligned_exact (pointer size : BitVec 64) (aligned : pointer.toNat % 8 = 0)
    (sized : size.toNat % 8 = 0) (bound : pointer.toNat + size.toNat ≤ 33806089496) :
    allocationEnd pointer size = pointer + size := by
  apply BitVec.eq_of_toNat_eq
  rw [allocationEnd_toNat pointer size bound,BitVec.toNat_add_of_lt (by omega)]
  omega

#print axioms allocationEnd_aligned_exact
end InitECandidate.Runtime
