import InitECandidate.Runtime.TransactionBodyBound
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.TrapNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned decoder execution has passed the empty-input guard and actual
byte load, reaching allocation with only b0 added to the local environment. -/
theorem transaction_body_returned_allocation {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (value : ValueHOL 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    0 < length.toNat ∧ ∃ entry output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState entry (transactionAt 2) = (some (.returned value),output) ∧
      entry.memory = state.memory ∧ entry.globals = state.globals ∧ entry.code = state.code ∧
      entry.memaddrs = state.memaddrs ∧ entry.clock = state.clock ∧
      (∀ name, name ≠ ofString "b0" → entry.locals.lookup name = state.locals.lookup name) ∧ post.memory = output.memory := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "len")) (.const 0)) =
      some (.val (.word (if length = (0 : BitVec 64) then (1 : BitVec 64) else 0))) := by
    by_cases zero : length = 0 <;> simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,zero]
  rw [source_transaction_body,evaluateHOLFiniteState_seq_line780] at run
  unfold transactionEmptyGuard at run
  rw [evaluateHOLFiniteState_ite,condition] at run
  by_cases zero : length = (0 : BitVec 64)
  · rw [if_pos zero] at run
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at run
    have noReturn := evaluate_raise_no_return state (ofString "TxErr") (.const 1) value
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 1)) with
    | mk result middle =>
      rw [raised] at run noReturn
      cases result with
      | none =>
        have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 1)
        rw [raised] at terminal
        exact False.elim (terminal rfl)
      | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
  · rw [if_neg zero] at run
    dsimp only at run
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_skip] at run
    have positive : 0 < length.toNat := by
      have nonzero : length.toNat ≠ 0 := fun equal => zero (BitVec.eq_of_toNat_eq equal)
      omega
    dsimp only at run
    rw [source_transaction_byte_scope] at run
    obtain ⟨byte,output,_,bodyRun,scope⟩ := evaluate_dec_returned_scope state post _ _ _ _ value run
    let entry := setVarHOLFinite (ofString "b0") byte state
    refine ⟨positive,entry,output,bodyRun,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro name different
      simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    · rw [scope]

#print axioms transaction_body_returned_allocation
end InitECandidate.Runtime
