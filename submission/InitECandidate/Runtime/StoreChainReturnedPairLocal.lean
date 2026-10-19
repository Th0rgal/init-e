import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Stores ending in an explicit tag and the unchanged record local. -/
inductive StoreChainReturnedPairLocal (key : MlS) (tag : BitVec 64) : ProgHOL 64 → Prop
  | finish : StoreChainReturnedPairLocal key tag (.return (.rstruct [.const tag,.var .local key]))
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (tail : StoreChainReturnedPairLocal key tag rest) :
      StoreChainReturnedPairLocal key tag (.seq (.store destination value) rest)

theorem evaluate_storeChain_returned_pair_local {F : Type} {key : MlS} {tag : BitVec 64} {program : ProgHOL 64}
    (supported : StoreChainReturnedPairLocal key tag program) (s post : PanSemStateFiniteExact 64 F)
    (word : BitVec 64) (value : ValueHOL 64)
    (atKey : s.locals.lookup key = some (.val (.word word)))
    (run : evaluateHOLFiniteState s program = (some (.returned value),post)) :
    value = .rStruct [.val (.word tag),.val (.word word)] := by
  induction supported generalizing s post with
  | finish =>
    have actual : evaluateHOLFiniteState s (.return (.rstruct [.const tag,.var .local key])) =
        (some (.returned (.rStruct [.val (.word tag),.val (.word word)])),emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atKey,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    exact (PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (actual.symm.trans run)).1)).symm
  | store destination expression tail ih =>
    have control := evaluate_store_control_frame s destination expression
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases stored : evaluateHOLFiniteState s (.store destination expression) with
    | mk result middle =>
      rw [stored] at run control
      dsimp only at run control
      rcases control.1 with rfl | rfl
      · exact ih middle post (by rw [control.2.1]; exact atKey) run
      · cases run

#print axioms evaluate_storeChain_returned_pair_local
end InitECandidate.Runtime
