import InitECandidate.Runtime.DecodeStepExtensionScratchProgress
import InitECandidate.Runtime.ScratchAllocationDecCallBound
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.MptFailCallTerminal
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed conditional failure guard has taken the skip arm. -/
theorem mpt_fail_guard_normal_state {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (failure : BitVec 64) (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (.ite condition
      (.call (some (none,none)) (ofString "mpt_fail") [.const failure]) .skip) = (none,post)) :
    post = s := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      exact (Prod.mk.inj run).2.symm
    · have terminal := evaluate_mptFail_call_terminal s (.const failure) failure code
        (by rw [evalListHOLFinite_eq_toExact]; rfl)
      exact False.elim (terminal (congrArg Prod.fst run))
  · cases run

/-- All actual extension-record stores and allocator rejection paths are bounded. -/
theorem runBounded_decode_step_extension_record {F : Type} (s : PanSemStateFiniteExact 64 F)
    (scratch frame : BitVec 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock) :
    RunBounded s decodeStepExtensionRecord 2 := by
  rw [source_decodeStep_extension_record]
  exact evaluate_scratch_alloc_decCall_straight_bounded s (.const 88) scratch 88 frame
    (ofString "rec") .one decodeStepExtensionStores
    (by rw [source_decodeStep_extension_stores]; rfl)
    (by rw [evalListHOLFinite_eq_toExact]; rfl) scratchGlobal frameGlobal code ticks

/-- The original empty-segment guard plus scratch-record construction is bounded
for every path-local value, including malformed locals and failed stores. -/
theorem runBounded_decode_step_extension_suffix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (scratch frame : BitVec 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ticks : 3 ≤ s.clock) :
    RunBounded s decodeStepExtensionSuffix 3 := by
  have fail : ProgBounded (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) 1 := by
    intro F state installed budget
    have bound := evaluate_mptFail_call_bounded state (.const 7) 7 installed (by omega)
      (by rw [evalListHOLFinite_eq_toExact]; rfl)
    exact ⟨by rw [bound.1]; omega,by rw [bound.1]; omega,bound.2.1⟩
  let guard : ProgHOL 64 := .ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0))
    (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) .skip
  have skipped : ProgBounded (.skip : ProgHOL 64) 0 := ProgBounded.straight .skip rfl
  have bound : ProgBounded guard 1 := ProgBounded.ite _ fail (ProgBounded.weaken skipped (by omega))
  rw [source_decodeStep_extension_suffix]
  apply RunBounded.seq (b := 2) (RunBounded.ofProg bound code (by omega)) ticks
  intro next normal nextCode budget
  have same := mpt_fail_guard_normal_state s next _ 7 code normal
  subst next
  exact runBounded_decode_step_extension_record s scratch frame scratchGlobal frameGlobal code budget

/-- Every successful original extension suffix consumes a real scratch record;
failed guards and malformed path locals cannot return a hidden push. -/
theorem decode_step_extension_suffix_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (ticks : 3 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepExtensionSuffix = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  rw [source_decodeStep_extension_suffix] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 7 code normal
  subst next
  exact decode_step_extension_record_returned_progress s post scratch frame value scratchGlobal frameGlobal
    ordered code (by omega) tailRun

#print axioms decode_step_extension_suffix_returned_progress
#print axioms mpt_fail_guard_normal_state
#print axioms runBounded_decode_step_extension_record
#print axioms runBounded_decode_step_extension_suffix
end InitECandidate.Runtime
