import InitECandidate.Runtime.RlpHeaderSingleByte
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty RLP input takes the original rlp_fail(1) call before any header
load, spending one tick and never returning an item. -/
theorem evaluate_rlpHeader_empty_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word (0 : BitVec 64))))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header)
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none ∧
      (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have bound := evaluate_rlpFail_call_bounded state (.const 1) 1 code (by omega) (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 1]
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_rlpHeader_body,evaluateHOLFiniteState_seq_line780,check]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) with
  | mk result post =>
    rw [run] at bound noReturn
    dsimp only at bound noReturn
    cases result with
    | none => exact False.elim (bound.2.2 rfl)
    | some stopped => exact ⟨bound.1,bound.2.1,bound.2.2,noReturn⟩

/-- An unreadable initial byte stops the original header parser immediately,
without entering later cases or spending any source clock. -/
theorem evaluate_rlpHeader_unreadable_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = none) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some .error,state) := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  rw [source_rlpHeader_body,evaluateHOLFiniteState_seq_line780,check]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  simp [evalHOLExact,pointerLocal,loaded]

#print axioms evaluate_rlpHeader_empty_body
#print axioms evaluate_rlpHeader_unreadable_header
end InitECandidate.Runtime
