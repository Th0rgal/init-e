import InitECandidate.Runtime.SszSplitVarListEval
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Memory after one accepted iteration: the previous slice length (when i > 0)
and the current slice pointer. -/
def sszSplitStepMemory (m : BitVec 64 → HolWordLab 64) (arr p i o prev : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  wmem (if Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true then wmem m (arr + (i - 1) * 16 + 8) (o - prev) else m)
    (arr + i * 16) (p + o)

theorem sszsplit_names :
    ofString "o" ≠ ofString "p" ∧ ofString "o" ≠ ofString "len" ∧ ofString "o" ≠ ofString "first" ∧
    ofString "o" ≠ ofString "count" ∧ ofString "o" ≠ ofString "arr" ∧ ofString "o" ≠ ofString "i" ∧
    ofString "o" ≠ ofString "prev" ∧ ofString "i" ≠ ofString "p" ∧ ofString "i" ≠ ofString "len" ∧
    ofString "i" ≠ ofString "first" ∧ ofString "i" ≠ ofString "count" ∧ ofString "i" ≠ ofString "arr" ∧
    ofString "i" ≠ ofString "prev" ∧ ofString "prev" ≠ ofString "p" ∧ ofString "prev" ≠ ofString "len" ∧
    ofString "prev" ≠ ofString "first" ∧ ofString "prev" ≠ ofString "count" ∧ ofString "prev" ≠ ofString "arr" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

theorem sszSplit_assign_prev {σ : Type} (c : PanSemStateFiniteExact 64 σ) (o prev : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word o)))
    (hp : c.locals.lookup (ofString "prev") = some (.val (.word prev))) :
    evaluateHOLFiniteState c (.assign .local (ofString "prev") (sszLocal "o")) =
      (none, setVarHOLFinite (ofString "prev") (.val (.word o)) c) := by
  simp [sszLocal, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, ho, hp, lookupKvarHOLExact,
    isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]

theorem sszSplit_assign_i {σ : Type} (c : PanSemStateFiniteExact 64 σ) (i : BitVec 64)
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    evaluateHOLFiniteState c (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (i + 1))) c) := by
  simp [sszLocal, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, lookupKvarHOLExact,
    isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem sszSplit_guard_i {σ : Type} (c : PanSemStateFiniteExact 64 σ) (i : BitVec 64)
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.cmp .less (.const 0) (sszLocal "i")) =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true then 1#64 else 0#64))) := by
  simp [sszLocal, evalHOLExact, hi, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true <;> simp [h]

end InitECandidate.Runtime
