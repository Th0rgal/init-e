import InitECandidate.Runtime.TransactionChainIdIndex
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual type guard determines the next decoder index. -/
theorem transaction_chain_id_index_by_kind {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index kind : BitVec 64)
    (binding : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if kind = 0#64 then index else 1))) := by
  unfold transactionChainIdBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  by_cases legacy : kind = 0#64
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,legacy]
    rw [condition] at run
    dsimp only at run
    rw [evaluateHOLFiniteState_skip] at run
    cases run
    simpa only [if_pos legacy] using binding
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,legacy]
    rw [condition] at run
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0),evaluateHOLFiniteState_seq_line780] at run
    cases called : evaluateHOLFiniteState state
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments) with
    | mk result middle =>
      rw [called] at run
      cases result with
      | some result => cases run
      | none =>
        simpa only [if_neg legacy] using transaction_chain_id_finish_index middle post run

#print axioms transaction_chain_id_index_by_kind
end InitECandidate.Runtime
