import InitECandidate.Runtime.SourceDomainTransferAt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Exact loop induction step. The body and recursive-loop transfer facts
are required only for the actual condition, decremented entry clock and
actual normally completing/continuing body states. Break and other results
are propagated with identical states and remaining clocks. -/
theorem source_domain_transfer_while_at {F : Type} (s : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (body : ProgHOL 64)
 (bodyTransfer : ∀w : BitVec 64,
  @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word w))→
  w≠0→s.clock≠0→SourceDomainRunTransferAt body (decClockHOLFinite s))
 (againTransfer : ∀(w : BitVec 64) bodyResult middle,
  @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word w))→
  w≠0→s.clock≠0→evaluateHOLFiniteState (decClockHOLFinite s) body=(bodyResult,middle)→
  (bodyResult=none ∨bodyResult=some .continue)→SourceDomainRunTransferAt (.while condition body) middle) :
 SourceDomainRunTransferAt (.while condition body) s := by
 intro domain subset result post run valid
 rw [evaluateHOLFiniteState_while_fixClockRewrite,evalHOLFinite_eq_toExact] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) condition with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset condition value actual]
  cases value with
  | val payload=>
   cases payload with
   | word w=>
    dsimp only at run ⊢
    by_cases positive : w≠0
    · rw [if_pos positive] at run ⊢
      by_cases zero : s.clock=0
      · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_pos zero] at run ⊢
        cases run
        rfl
      · simp only [show ({s with memaddrs:=domain}).clock=s.clock from rfl,if_neg zero] at run ⊢
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk bodyResult middle=>
         rw [bodyRun] at run
         have bodyValid : bodyResult≠some .error := by
          intro failed
          rw [failed] at run
          exact valid (Prod.mk.inj run).1.symm
         have widened:=(bodyTransfer w actual positive zero) domain subset bodyResult middle bodyRun bodyValid
         change evaluateHOLFiniteState (decClockHOLFinite {s with memaddrs:=domain}) body=
          (bodyResult,{middle with memaddrs:=domain}) at widened
         rw [widened]
         have metadata:=evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
         rw [bodyRun] at metadata
         have middleSubset : ∀address,middle.memaddrs address→domain address := by
          intro address accessible
          apply subset address
          rw [←show middle.memaddrs=s.memaddrs from metadata.2.1]
          exact accessible
         cases bodyResult with
         | none=>
          exact (againTransfer w none middle actual positive zero bodyRun (Or.inl rfl))
           domain middleSubset result post run valid
         | some bodyResult=>
          cases bodyResult with
          | «continue»=>
           exact (againTransfer w (some .continue) middle actual positive zero bodyRun (Or.inr rfl))
            domain middleSubset result post run valid
          | error=>exact False.elim (bodyValid rfl)
          | «break»=>cases run;rfl
          | returned value=>cases run;rfl
          | timeOut=>cases run;rfl
          | exception name value=>cases run;rfl
          | finalFfi event=>cases run;rfl
    · rw [if_neg positive] at run ⊢
      cases run
      rfl
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_while_at
end InitECandidate.Runtime
