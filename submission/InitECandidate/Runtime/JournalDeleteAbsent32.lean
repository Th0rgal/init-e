import InitECandidate.Runtime.JournalDeleteSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Missing-key journal deletion returns before allocating or writing a record. -/
theorem evaluate_journalDelete_absent32 {F : Type} (state : PanSemStateFiniteExact 64 F) (value : BitVec 64)
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word value)])) :
    evaluateHOLFiniteState state journalDeleteAfterGet32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite state) := by
  have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,old,Compiler.Encoders.Asm.wordCmpHOL]
  have returned : evaluateHOLFiniteState state (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite state) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have selected : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite state) := by
    rw [evaluateHOLFiniteState_ite,condition]
    exact returned
  unfold journalDeleteAfterGet32
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState,selected]

#print axioms evaluate_journalDelete_absent32
end InitECandidate.Runtime
