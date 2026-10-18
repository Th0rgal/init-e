import InitECandidate.Runtime.TransactionFeeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original fee conditional consumes one legacy fee or two dynamic fees. -/
theorem transaction_fee_normal_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind index : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionFeeBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (index + (if 1#64 < kind then 2 else 1)))) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 1) (.var .local (ofString "t"))) =
      some (.val (.word (if 1#64 < kind then (0 : BitVec 64) else 1))) := by
    have ordering : kind ≤ 1#64 ↔ ¬1#64 < kind := by
      rw [BitVec.le_def,BitVec.lt_def]
      omega
    by_cases higher : 1#64 < kind <;>
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,ordering,higher]
  unfold transactionFeeBranch at run
  rw [evaluateHOLFiniteState_ite,condition] at run
  by_cases higher : 1#64 < kind
  · rw [if_pos higher] at run ⊢
    dsimp only at run
    rw [if_pos rfl] at run
    exact transactionFeeDynamic_adds_two state post index indexLocal run
  · rw [if_neg higher] at run ⊢
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at run
    exact transactionFeeLegacy_adds_one state post index indexLocal run

#print axioms transaction_fee_normal_index
end InitECandidate.Runtime
