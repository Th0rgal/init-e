import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.TransactionTopScopeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned execution passes through all three original parser declarations.
Their temporary bindings affect only locals; every memory/global/clock premise
can be transported to the actual type-dispatch entry. -/
theorem transaction_parsing_scopes_returned_initialized {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 6) = (some (.returned returned),post)) :
    ∃ entry output : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState entry (transactionAt 9) = (some (.returned returned),output) ∧
      entry.memory = state.memory ∧ entry.globals = state.globals ∧ entry.code = state.code ∧
      entry.memaddrs = state.memaddrs ∧ entry.clock = state.clock ∧
      (∀ name, name ≠ ofString "top" → name ≠ ofString "t" → name ≠ ofString "nfields" →
        entry.locals.lookup name = state.locals.lookup name) ∧ entry.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))) ∧
      entry.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))) ∧ post.memory = output.memory := by
  rw [source_transaction_top_scope] at run
  obtain ⟨top,middle,_,topRun,topScope⟩ := evaluate_dec_returned_scope state post _ _ _ _ returned run
  let enteredTop := setVarHOLFinite (ofString "top") top state
  rw [source_transaction_t_scope] at topRun
  obtain ⟨kind,next,kindInitial,kindRun,kindScope⟩ := evaluate_dec_returned_scope enteredTop middle _ _ _ _ returned topRun
  have kindEq : kind = .val (.word (0 : BitVec 64)) := by
    simpa only [evalHOLExact,Option.some.injEq] using kindInitial.symm
  subst kind
  let enteredKind := setVarHOLFinite (ofString "t") (.val (.word (0 : BitVec 64))) enteredTop
  rw [source_transaction_nfields_scope] at kindRun
  obtain ⟨count,output,countInitial,bodyRun,countScope⟩ := evaluate_dec_returned_scope enteredKind next _ _ _ _ returned kindRun
  have countEq : count = .val (.word (9 : BitVec 64)) := by
    simpa only [evalHOLExact,Option.some.injEq] using countInitial.symm
  subst count
  let entry := setVarHOLFinite (ofString "nfields") (.val (.word (9 : BitVec 64))) enteredKind
  refine ⟨entry,output,bodyRun,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
  · intro name notTop notKind notCount
    simp [entry,enteredKind,enteredTop,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notTop,Ne.symm notKind,Ne.symm notCount]
  · simp [entry,enteredKind,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "nfields" ≠ ofString "t" by decide]
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [topScope,kindScope,countScope]

#print axioms transaction_parsing_scopes_returned_initialized
end InitECandidate.Runtime
