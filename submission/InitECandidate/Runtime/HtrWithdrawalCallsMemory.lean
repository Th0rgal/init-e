import InitECandidate.Runtime.HtrWithdrawalSecondMemory
import InitECandidate.Runtime.HtrU64AtMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrWithdrawal_calls_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes w roots heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atW : state.locals.lookup (ofString "w") = some (.val (.word w)))
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 128 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atPacked : state.locals.lookup (ofString "ch") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : withdrawalCallsCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrWithdrawalAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.var .local (ofString "w"),.var .local (ofString "ch")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word w),.val (.word roots)] := by
    simp [arguments,evalListHOLExact,evalHOLExact,atW,atPacked,wordOpHOL,wordOp,valueIsWord,valueWord]
  have firstBudget : 30 ≤ state.clock := (Nat.le_add_right _ _).trans budget
  rw [source_htrWithdrawal_u64_first] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_u64_at") arguments v) run
  have frame := htrU64At_call_normal_memory state middle arguments w roots watched
    args code rootsAligned (by omega) (Or.inl rootsBefore) firstBudget normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_u64_at") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = _ at normal
    simpa only [normal] using kept
  have globals := htrU64At_call_globals arguments state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_u64_at") arguments)
  change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = _ at normal
  rw [normal] at globals metadata
  have callBound := RunBounded.ofProg (ProgBounded.call htrU64At_funBounded none arguments) code firstBudget
  unfold RunBounded at callBound
  rw [normal] at callBound
  have enough : withdrawalSecondCost ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + 30 := callBound.1
    change 30 + withdrawalSecondCost ≤ state.clock at budget
    omega
  have remaining := htrWithdrawal_second_suffix_returned_memory middle post pointer accelerator zeroHashes w roots heap out mark watched value
    ((keep _).trans atW) rootsAligned rootsFits rootsBefore
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) ((keep _).trans atMark)
    (by rw [globals]; exact atZero) ((keep _).trans atPacked) (by rw [globals]; exact hh) ((keep _).trans atOut)
    outAligned outFits outOutside heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside (metadata.1.trans code) enough tail
  exact remaining.trans frame

#print axioms htrWithdrawal_calls_suffix_returned_memory
end InitECandidate.Runtime
