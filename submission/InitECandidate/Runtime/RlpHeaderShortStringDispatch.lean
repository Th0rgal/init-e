import InitECandidate.Runtime.RlpHeaderShortStringContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The loaded-byte dispatch selects short strings and their terminal result
prevents every later header branch from executing. -/
theorem evaluate_rlpHeader_short_string_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    evaluateHOLFiniteState state rlpHeaderAfterByte = evaluateHOLFiniteState state rlpHeaderShortStringBranch := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128)) rlpHeaderSingleBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,post,run,_,_,_,terminal,_⟩ := evaluate_rlpHeader_short_string_contract state header total
    headerLocal totalLocal lower upper nonzero code ticks
  rw [source_rlpHeaderSingle_dispatch,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpHeaderShortString_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [run]
  cases result with
  | none => exact False.elim (terminal rfl)
  | some stopped => rfl

#print axioms evaluate_rlpHeader_short_string_after_load
end InitECandidate.Runtime
