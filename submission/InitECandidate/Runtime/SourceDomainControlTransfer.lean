import InitECandidate.Runtime.SourceDomainProgramTransfer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A non-error conditional takes exactly the same branch in the larger domain. -/
theorem source_domain_transfer_ite (condition : ExpHOL 64) {yes no : ProgHOL 64}
 (yesTransfer : SourceDomainRunTransfer yes) (noTransfer : SourceDomainRunTransfer no) :
 SourceDomainRunTransfer (.ite condition yes no) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_ite] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) condition with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset condition value actual]
  cases value with
  | val word=>
   cases word with
   | word w=>
    dsimp only at run ⊢
    by_cases zero : w=0
    · rw [if_pos zero] at run ⊢
      exact noTransfer s domain subset result post run valid
    · rw [if_neg zero] at run ⊢
      exact yesTransfer s domain subset result post run valid
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

/-- Local/global assignment preserves its actual successful expression and
shape check, with the domain update commuting with the resulting assignment. -/
theorem source_domain_transfer_assign (kind : VarKind) (name : MlS) (expression : ExpHOL 64) :
 SourceDomainRunTransfer (.assign kind name expression) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_assign] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset expression value actual]
  have same : isValidValueHOLFinite ({s with memaddrs:=domain}) kind name value=
   isValidValueHOLFinite s kind name value := by cases kind <;>rfl
  dsimp only at run ⊢
  rw [same]
  by_cases assignable : isValidValueHOLFinite s kind name value=true
  · rw [if_pos assignable] at run ⊢
    cases run
    cases kind <;>rfl
  · rw [if_neg assignable] at run
    exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_ite
#print axioms source_domain_transfer_assign
end InitECandidate.Runtime
