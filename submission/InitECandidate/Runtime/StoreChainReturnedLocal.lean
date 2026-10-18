import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Stores followed by a return of an unchanged local variable. -/
inductive StoreChainReturnedLocal (key : MlS) : ProgHOL 64 → Prop
  | finish : StoreChainReturnedLocal key (.return (.var .local key))
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (tail : StoreChainReturnedLocal key rest) :
      StoreChainReturnedLocal key (.seq (.store destination value) rest)

theorem evaluate_storeChain_returned_local {F : Type} {key : MlS} {program : ProgHOL 64}
    (supported : StoreChainReturnedLocal key program) (state post : PanSemStateFiniteExact 64 F)
    (word : BitVec 64) (value : ValueHOL 64)
    (atKey : state.locals.lookup key = some (.val (.word word)))
    (run : evaluateHOLFiniteState state program = (some (.returned value),post)) :
    value = .val (.word word) := by
  induction supported generalizing state post with
  | finish =>
    have actual : evaluateHOLFiniteState state (.return (.var .local key)) =
        (some (.returned (.val (.word word))),emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,atKey,shapeOfHOLExact]
    have equal := (Prod.mk.inj (actual.symm.trans run)).1
    exact (PanSemResultExact.returned.inj (Option.some.inj equal)).symm
  | store destination expression tail ih =>
    have control := evaluate_store_control_frame state destination expression
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases stored : evaluateHOLFiniteState state (.store destination expression) with
    | mk result middle =>
      rw [stored] at run control
      dsimp only at run control
      rcases control.1 with rfl | rfl
      · exact ih middle post (by rw [control.2.1]; exact atKey) run
      · cases run

#print axioms evaluate_storeChain_returned_local
end InitECandidate.Runtime
