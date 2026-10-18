import InitECandidate.Runtime.InputBlobSource
import InitECandidate.Runtime.ConditionalTrapBound
import InitECandidate.Runtime.StatelessPrefixStages
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem inputBlob_guard_flag {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (atLength : state.locals.lookup (ofString "len") = some (.val (.word length))) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.const 134217712) (.var .local (ofString "len"))) =
        some (.val (.word (if 134217712 < length.toNat then 1 else 0))) := by
  simp [evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- Input lengths within the declared input buffer pass without a tick. -/
theorem inputBlob_guard_accepts {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (small : length.toNat ≤ 134217712) : evaluateHOLFiniteState state inputBlobGuard = (none,state) := by
  rw [inputBlobGuard,evaluateHOLFiniteState_ite,inputBlob_guard_flag state length atLength]
  simp [show ¬134217712 < length.toNat by omega,evaluateHOLFiniteState_skip]

/-- A normal return from the actual pre-allocation guard certifies the
declared length fits the input buffer and leaves the state unchanged. -/
theorem inputBlob_guard_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state inputBlobGuard = (none,post)) :
    length.toNat ≤ 134217712 ∧ post = state := by
  rw [inputBlobGuard,evaluateHOLFiniteState_ite,inputBlob_guard_flag state length atLength] at run
  by_cases large : 134217712 < length.toNat
  · simp only [if_pos large] at run
    rw [if_neg (by decide : ¬ (1 : BitVec 64) = 0)] at run
    have terminal := evaluate_trap_call_terminal state (.const 8) 8 code (by rfl)
    rw [run] at terminal
    exact (terminal rfl).elim
  · simp only [if_neg large] at run
    simp only [if_true,evaluateHOLFiniteState_skip] at run
    exact ⟨by omega,(Prod.mk.inj run).2.symm⟩

/-- Every oversized declared input terminates at the original rejection
trap before reaching the allocator or copy loop. This is the input-buffer
trap code 8, with at most one source tick, including early host termination. -/
theorem inputBlob_oversized_rejected {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (large : 134217712 < length.toNat) (budget : 1 ≤ state.clock) :
    StAbort state (evaluateHOLFiniteState state (inputBlobAt 2)) 1 := by
  have guard := evaluate_conditional_trap_bounded state
    (.cmp .lower (.const 134217712) (.var .local (ofString "len"))) 8 code budget
  obtain ⟨result,post,run,spent,kept,safe,_,nr⟩ := guard
  change evaluateHOLFiniteState state inputBlobGuard = (result,post) at run
  have actual : evaluateHOLFiniteState state inputBlobGuard =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 8]) := by
    rw [inputBlobGuard,evaluateHOLFiniteState_ite,inputBlob_guard_flag state length atLength]
    simp [large]
  have terminal := evaluate_trap_call_terminal state (.const 8) 8 code (by rfl)
  rw [← actual,run] at terminal
  cases result with
  | none => exact (terminal rfl).elim
  | some result =>
    have aborted : StAbort state (evaluateHOLFiniteState state inputBlobGuard) 1 := by
      rw [run]
      exact ⟨result,rfl,(fun value equal => nr value (by rw [equal])),spent,kept,
        fun _ equal => safe (by rw [equal])⟩
    rw [source_inputBlob_stages.2.2.1]
    exact stAbort_seq state inputBlobGuard (inputBlobAt 3) 1 aborted

#print axioms inputBlob_guard_normal
#print axioms inputBlob_oversized_rejected
end InitECandidate.Runtime
