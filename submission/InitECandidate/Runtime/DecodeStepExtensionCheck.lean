import InitECandidate.Runtime.DecodeStepCompactCall
import InitECandidate.Runtime.MptFailCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepLeafBranch : ProgHOL 64 :=
  match decodeStepCompactContinuation with
  | .seq (.ite _ body _) _ => body
  | _ => .skip

def decodeStepExtensionSuffix : ProgHOL 64 :=
  match decodeStepCompactContinuation with
  | .seq _ body => body
  | _ => .skip

def decodeStepExtensionRecord : ProgHOL 64 :=
  match decodeStepExtensionSuffix with
  | .seq _ body => body
  | _ => .skip

theorem source_decodeStep_path_dispatch : decodeStepCompactContinuation =
    .seq (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "cn"))) (.const 0))
      decodeStepLeafBranch .skip) decodeStepExtensionSuffix := by
  simp only [decodeStepCompactContinuation,decodeStepCompactCall,decodeStepLeafBranch,
    decodeStepExtensionSuffix,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_decodeStep_extension_suffix : decodeStepExtensionSuffix =
    .seq (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) .skip) decodeStepExtensionRecord := by
  simp only [decodeStepExtensionSuffix,decodeStepExtensionRecord,decodeStepCompactContinuation,decodeStepCompactCall,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A non-leaf decoded header enters exactly the original extension suffix. -/
theorem evaluate_decodeStep_extension_dispatch {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64)
    (localPath : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word pointer),.val (.word count),.val (.word (0 : BitVec 64))])) :
    evaluateHOLFiniteState state decodeStepCompactContinuation = evaluateHOLFiniteState state decodeStepExtensionSuffix := by
  rw [source_decodeStep_path_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,localPath,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

/-- Normal extension parsing cannot pass the original empty-segment error
check; the following record code runs in the same state with a positive count. -/
theorem evaluate_decodeStep_extension_nonempty {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count leaf : BitVec 64)
    (localPath : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word pointer),.val (.word count),.val (.word leaf)]))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state decodeStepExtensionSuffix = (none,post)) :
    0 < count.toNat ∧ evaluateHOLFiniteState state decodeStepExtensionRecord = (none,post) := by
  by_cases zero : count = 0
  · have fail := evaluate_mptFail_call_bounded state (.const 7) 7 code (by omega) (by rfl)
    rw [source_decodeStep_extension_suffix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
    simp only [evalHOLExact,localPath,zero,List.getElem?_cons_zero,List.getElem?_cons_succ] at run
    simp only [Compiler.Encoders.Asm.wordCmpHOL,beq_self_eq_true,if_true] at run
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) with
    | mk result output =>
      rw [called] at fail
      dsimp only at fail
      cases result with
      | none => exact False.elim (fail.2.2 rfl)
      | some stopped =>
        simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false,called] at run
        cases run
  · have notZero : count ≠ BitVec.ofNat 64 0 := zero
    have check : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0))
          (.call (some (none,none)) (ofString "mpt_fail") [.const 7]) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite]
      simp [evalHOLExact,localPath,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
    rw [source_decodeStep_extension_suffix,evaluateHOLFiniteState_seq_line780,check] at run
    refine ⟨?_,run⟩
    by_contra h
    apply zero
    apply BitVec.eq_of_toNat_eq
    simpa using (show count.toNat = 0 by omega)

#print axioms evaluate_decodeStep_extension_dispatch
#print axioms evaluate_decodeStep_extension_nonempty
end InitECandidate.Runtime
