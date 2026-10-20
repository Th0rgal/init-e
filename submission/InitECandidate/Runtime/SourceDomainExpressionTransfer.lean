import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Successful canonical expression evaluation is preserved by enlarging the
ordinary word-cell domain. This adapter changes only the domain, never memory,
locals, byte order or the expression. It is a prerequisite for program-level
transfer, not a program/runtime bound by itself. -/
theorem eval_source_domain_extend {F : Type} (s : PanSemStateFiniteExact 64 F)
 (domain : BitVec 64→Prop) (subset : ∀address,s.memaddrs address→domain address)
 (expression : ExpHOL 64) (value : ValueHOL 64)
 (run : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some value) :
 @evalHOLExact 64 F _ ({s with memaddrs:=domain}).toExact
  (fun a=>Classical.propDecidable (domain a)) expression=some value := by
 classical
 let localState:=PanPropsEvalStateFiniteExact.ofPanSemFinite s
 have evaluated : localState.evalHOL expression=some value:=run
 have widened:=PanPropsEvalStateFiniteExact.evalSwapMemaddrsHOLFinite localState expression value domain
  ⟨evaluated,subset⟩
 exact widened

#print axioms eval_source_domain_extend

/-- Every successful actual call-argument list evaluates to the same values
in the enlarged ordinary-memory domain. Missing actual reads are not assumed
to succeed, and this statement does not identify an unaligned word with bytes. -/
theorem eval_list_source_domain_extend {F : Type} (s : PanSemStateFiniteExact 64 F)
 (domain : BitVec 64→Prop) (subset : ∀address,s.memaddrs address→domain address)
 (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64))
 (run : @evalListHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expressions=some values) :
 @evalListHOLExact 64 F _ ({s with memaddrs:=domain}).toExact
  (fun a=>Classical.propDecidable (domain a)) expressions=some values := by
 induction expressions generalizing values with
 | nil=>simpa only [evalListHOLExact] using run
 | cons expression rest ih=>
  cases first : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
  | none=>simp [evalListHOLExact,first] at run
  | some value=>
   cases remaining : @evalListHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) rest with
   | none=>simp [evalListHOLExact,first,remaining] at run
   | some tail=>
    have firstWide:=eval_source_domain_extend s domain subset expression value first
    have restWide:=ih tail remaining
    simpa only [evalListHOLExact,firstWide,restWide,first,remaining] using run

#print axioms eval_list_source_domain_extend
end InitECandidate.Runtime
