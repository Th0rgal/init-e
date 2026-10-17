import InitECandidate.Runtime.RlpHeaderLongStringContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Long-string bytes select the original terminal long-string header branch. -/
theorem evaluate_rlpHeader_long_string_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    evaluateHOLFiniteState state rlpHeaderAfterByte = evaluateHOLFiniteState state rlpHeaderLongString := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128)) rlpHeaderSingleBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpHeaderShortStringBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,post,run,_⟩ := evaluate_rlpHeader_long_string_bounded state pointer header pointerLocal headerLocal
    lower upper code ticks
  have terminal := evaluate_rlpHeader_long_string_terminal state pointer header pointerLocal headerLocal lower upper code ticks
  rw [run] at terminal
  rw [source_rlpHeaderSingle_dispatch,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpHeaderShortString_dispatch,evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  rw [source_rlpHeaderLongString_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  simp only [rlpHeaderLongString] at run ⊢
  rw [run]
  cases result with
  | none => exact False.elim (terminal rfl)
  | some stopped => rfl

#print axioms evaluate_rlpHeader_long_string_after_load
end InitECandidate.Runtime
