import InitECandidate.Runtime.RlpDecodeFullyContinuation
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful full decoding returns the unchanged four-word item and
proves that its consumed field equals the supplied input length. -/
theorem rlpDecodeFully_continuation_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind pointer payload consumed total : BitVec 64) (value : ValueHOL 64)
    (itemLocal : state.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word payload),.val (.word consumed)]))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpDecodeFullyContinuation = (some (.returned value),post)) :
    value = .rStruct [.val (.word kind),.val (.word pointer),.val (.word payload),.val (.word consumed)] ∧ consumed = total := by
  by_cases matched : consumed = total
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len"))) =
        some (.val (.word 0)) := by
      simp [evalHOLExact,itemLocal,totalLocal,Compiler.Encoders.Asm.wordCmpHOL,matched]
    rw [source_rlpDecodeFully_continuation,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [evaluateHOLFiniteState_skip,ite_true] at run
    have returned : evaluateHOLFiniteState state (.return (.var .local (ofString "it"))) =
        (some (.returned (.rStruct [.val (.word kind),.val (.word pointer),.val (.word payload),.val (.word consumed)])),
          emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,itemLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [returned] at run
    have equal := (Prod.mk.inj run).1
    exact ⟨by simpa using equal.symm,matched⟩
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len"))) =
        some (.val (.word 1)) := by
      simp [evalHOLExact,itemLocal,totalLocal,Compiler.Encoders.Asm.wordCmpHOL,matched]
    rw [source_rlpDecodeFully_continuation,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have terminal := evaluate_rlpFail_call_terminal state (.const 6) 6 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 6] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 6]) with
    | mk result output =>
      rw [called] at terminal noReturn run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)

#print axioms rlpDecodeFully_continuation_return_contract
end InitECandidate.Runtime
