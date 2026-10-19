import InitECandidate.Runtime.ProgressiveFoldSuffixMemory
import InitECandidate.Runtime.MemzeroNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveZero_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator roots acc initial out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atK : state.locals.lookup (ofString "k") = some (.val (.word initial)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ 4 * 134217712)
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 16 + (progressiveFoldCost + 16) ≤ state.clock)
    (run : evaluateHOLFiniteState state (progressiveAt 7) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "acc"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word acc),.val (.word (32#64))] := by simp [arguments,evalListHOLExact,evalHOLExact,atAcc]
  rw [source_progressive_zero] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memzero") arguments v) run
  obtain ⟨frame,locals⟩ := memzero_call_normal_memory state middle arguments acc (32#64) watched args code
    accAligned accFits (Or.inl accBefore) normal
  have clocks := (memzero_const_progBounded (.var .local (ofString "acc")) 32 (by decide)) state code
    ((Nat.le_add_right 16 _).trans budget)
  have globals := memzero_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memzero") arguments)
  change RunBounded state (.call (some (none,none)) (ofString "memzero") arguments) 16 at clocks
  unfold RunBounded at clocks
  rw [normal] at clocks globals meta'
  have spent : state.clock ≤ middle.clock + 16 := clocks.1
  have enough : progressiveFoldCost + 16 ≤ middle.clock := by
    exact Nat.le_of_add_le_add_right
      ((show (progressiveFoldCost + 16) + 16 ≤ state.clock from by simpa only [Nat.add_comm] using budget).trans spent)
  have suffix := progressiveFold_suffix_returned_memory middle post pointer accelerator roots acc initial out mark watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel)
    (by rw [locals]; exact atRoots) (by rw [locals]; exact atAcc) (by rw [locals]; exact atK)
    (by rw [locals]; exact atOut) (by rw [locals]; exact atMark)
    outAligned outFits outOutside small accAligned accFits accBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside (meta'.1.trans code) enough tail
  exact suffix.trans frame

#print axioms progressiveZero_suffix_returned_memory
end InitECandidate.Runtime
