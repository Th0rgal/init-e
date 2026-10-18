import InitECandidate.Runtime.SszCheckOffsetsSource
import InitECandidate.Runtime.SszFailCallControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem orop_eq (x y : BitVec 64) : OrOp.or x y = x ||| y := rfl

theorem sszCheckRange_pass {σ : Type} (c : PanSemStateFiniteExact 64 σ) (w fixed len : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word w)))
    (hf : c.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (ok : ¬ w < fixed ∧ ¬ len < w) :
    evaluateHOLFiniteState c sszCheckRange = (none, c) := by
  unfold sszCheckRange
  simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hf, hl, ok.1, ok.2,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq]

theorem sszCheckRange_fail {σ : Type} (c : PanSemStateFiniteExact 64 σ) (w fixed len : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word w)))
    (hf : c.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (bad : w < fixed ∨ len < w) :
    evaluateHOLFiniteState c sszCheckRange =
      evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 10]) := by
  unfold sszCheckRange
  have value : (if w < fixed then 1#64 else 0#64) ||| (if len < w then 1#64 else 0#64) ≠ 0#64 := by
    rcases bad with bad | bad <;> simp [bad] <;> split <;> decide
  simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hf, hl,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq,
    Ne.symm value, -evaluateHOLFiniteState_call]

#print axioms sszCheckRange_pass
#print axioms sszCheckRange_fail

open Classical in
/-- Ordering check, evaluated against the actual previous offset load. -/
theorem sszCheckPrevious_eval {σ : Type} (c : PanSemStateFiniteExact 64 σ) (w offs i : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word w)))
    (hoffs : c.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    evaluateHOLFiniteState c sszCheckPrevious =
      if Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i then
        (if c.memaddrs (offs + i * 8#64 - 8#64) then
          (match c.memory (offs + i * 8#64 - 8#64) with
           | .word prev => if w < prev then
               evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 11]) else (none, c))
         else (some .error, c))
      else (none, c) := by
  unfold sszCheckPrevious sszOffsetAddress
  by_cases positive : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true
  · by_cases domain : c.memaddrs (offs + i * 8#64 - 8#64)
    · cases mem : c.memory (offs + i * 8#64 - 8#64) with
      | word prev =>
        by_cases less : w < prev
        · simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hoffs, hi, positive, domain, mem,
            less, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
            panOpHOL, memLoadHOLExact, isWfShapeExactHOL, -evaluateHOLFiniteState_call]
        · simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hoffs, hi, positive, domain, mem,
            less, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
            panOpHOL, memLoadHOLExact, isWfShapeExactHOL, -evaluateHOLFiniteState_call]
    · simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hoffs, hi, positive, domain,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
        panOpHOL, memLoadHOLExact, isWfShapeExactHOL, -evaluateHOLFiniteState_call]
  · simp [evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, hi, positive,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

#print axioms sszCheckPrevious_eval
end InitECandidate.Runtime
