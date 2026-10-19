import InitECandidate.Runtime.HtrWithdrawalThirdMemory
import InitECandidate.Runtime.HtrBytesVectorMemory
import InitECandidate.Runtime.HtrBytesVectorGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrWithdrawal_vector_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (code : state.code = originalRuntimeCode) (budget : withdrawalVectorCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrWithdrawalAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "w"),.const 16],.const 20,.op .add [.var .local (ofString "ch"),.const 64]]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (w + (16#64))),.val (.word (20#64)),.val (.word (roots + (64#64)))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,atW,atPacked,wordOpHOL,wordOp,valueIsWord,valueWord]
  have natural : (roots + (64#64)).toNat = roots.toNat + 64 := by
    apply BitVec.toNat_add_of_lt
    change roots.toNat + 64 < 2 ^ 64
    omega
  have aligned : (roots + (64#64)).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,rootsAligned]
  have firstBudget : htrBytesVectorBodyCost + 1 ≤ state.clock := (Nat.le_add_right _ _).trans budget
  rw [source_htrWithdrawal_vector] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_bytes_vector") arguments v) run
  have frame := htrBytesVector_call_normal_memory state middle arguments pointer accelerator zeroHashes
    (w + (16#64)) (20#64) heap (roots + (64#64)) watched args atPointer atAccel atZero hh
    aligned (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) (by decide)
    heapAligned heapFits heapBefore accelAligned accelFits pointerFits accelOutside pointerOutside code firstBudget normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_bytes_vector") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = _ at normal
    simpa only [normal] using kept
  have globals := htrBytesVector_call_normal_globals state middle arguments (w + (16#64)) (20#64)
    (roots + (64#64)) heap args hh code normal
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments)
  change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = _ at normal
  rw [normal] at metadata
  have callBound := runBounded_htrBytesVector_call state none arguments (w + (16#64)) (20#64)
    (roots + (64#64)) heap args (by decide) hh heapFits code firstBudget
  unfold RunBounded at callBound
  rw [normal] at callBound
  have enough : withdrawalThirdCost ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + (htrBytesVectorBodyCost + 1) := callBound.1
    change (htrBytesVectorBodyCost + 1) + withdrawalThirdCost ≤ state.clock at budget
    omega
  have remaining := htrWithdrawal_third_suffix_returned_memory middle post pointer accelerator zeroHashes w roots heap out mark watched value
    ((keep _).trans atW) rootsAligned rootsFits rootsBefore
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) ((keep _).trans atMark)
    (by rw [globals]; exact atZero) ((keep _).trans atPacked) (by rw [globals]; exact hh) ((keep _).trans atOut)
    outAligned outFits outOutside heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside (metadata.1.trans code) enough tail
  exact remaining.trans frame

#print axioms htrWithdrawal_vector_suffix_returned_memory
end InitECandidate.Runtime
