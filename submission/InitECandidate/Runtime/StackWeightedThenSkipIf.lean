import InitECandidate.Runtime.StackWeightedSkipIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-! The empty-then layout is literally the empty-else layout with the guard
negated. Transport the existing weighted traces instead of duplicating the
native branch and body proofs. -/

theorem weighted_thenSkipIf_flatten
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    Flapjack.Compiler.Backend.StackToLab.flattenHOL flag (.ite cmp reg operand .skip body)
      sectionId labelId continues breaks =
    Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip)
      sectionId labelId continues breaks := by
  cases cmp <;> simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL,
    Flapjack.Compiler.Backend.StackToLab.negateHOL, nonSkip,
    show Flapjack.Compiler.Backend.StackToLab.stackIsSkip (.skip : HolProg 64) = true from rfl,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem weighted_thenSkipIf_evaluate {F : Type}
    (body : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen) :
    StackSemEvaluate.evaluate (.ite cmp reg operand .skip body, source) =
    StackSemEvaluate.evaluate
      (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip, source) := by
  rw [StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_ite, lhs, rhs]
  dsimp only
  rw [Prelude.wordCmpNegate, condition]
  cases chosen <;> rfl

private theorem thenSkipIf_hyps {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen)
    (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) :
    FlattenHyps (.ite cmp reg operand .skip body) source flag result post
      sectionId labelId continues breaks start ↔
    FlattenHyps (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip)
      source flag result post sectionId labelId continues breaks start := by
  unfold FlattenHyps
  rw [weighted_thenSkipIf_evaluate body cmp reg operand source x y lhs rhs chosen condition,
    weighted_thenSkipIf_flatten body nonSkip cmp reg operand flag sectionId labelId continues breaks]
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs, and_true, true_and]

theorem normalWeightedFlatten_thenSkipIf_transport {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen)
    (price : LabProgHOL 64 → Nat → Nat)
    (bound : NormalWeightedFlatten
      (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip)
      source price) :
    NormalWeightedFlatten (.ite cmp reg operand .skip body) source price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  have converted := (thenSkipIf_hyps body nonSkip cmp reg operand source x y lhs rhs
    chosen condition flag _ post sectionId labelId continues breaks start).mp hyps
  rw [weighted_thenSkipIf_flatten body nonSkip cmp reg operand flag sectionId labelId continues breaks]
  exact bound flag post sectionId labelId continues breaks start encoded converted

theorem exitWeightedFlatten_thenSkipIf_transport {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bound : ExitWeightedFlatten
      (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip)
      source result price) :
    ExitWeightedFlatten (.ite cmp reg operand .skip body) source result price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  have converted := (thenSkipIf_hyps body nonSkip cmp reg operand source x y lhs rhs
    chosen condition flag _ post sectionId labelId continues breaks start).mp hyps
  exact bound flag post sectionId labelId continues breaks start encoded converted

theorem terminalWeightedFlatten_thenSkipIf_transport {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bound : TerminalWeightedFlatten
      (.ite (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand body .skip)
      source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand .skip body) source result outcome price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  have converted := (thenSkipIf_hyps body nonSkip cmp reg operand source x y lhs rhs
    chosen condition flag _ post sectionId labelId continues breaks start).mp hyps
  exact bound flag post sectionId labelId continues breaks start encoded converted

/-- Selecting the empty then arm costs only its taken branch. -/
theorem normalWeightedFlatten_thenSkipIf_true {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true) :
    NormalWeightedFlatten (.ite cmp reg operand .skip body) source (fun _ _ => 3) := by
  apply normalWeightedFlatten_thenSkipIf_transport body nonSkip cmp reg operand source x y lhs rhs true chosen
  apply normalWeightedFlatten_skipIf_false body nonSkip _ reg operand source x y lhs rhs
  rw [Prelude.wordCmpNegate, chosen]
  rfl

/-- A false guard executes the nonempty else arm, charging its actual work. -/
theorem normalWeightedFlatten_thenSkipIf_false {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyBound : NormalWeightedFlatten body source price) :
    NormalWeightedFlatten (.ite cmp reg operand .skip body) source
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  apply normalWeightedFlatten_thenSkipIf_transport body nonSkip cmp reg operand source x y lhs rhs false chosen
  apply normalWeightedFlatten_skipIf_true body nonSkip _ reg operand source x y lhs rhs _ price bodyBound
  rw [Prelude.wordCmpNegate, chosen]
  rfl

/-- A false guard executes the nonempty else arm, charging its actual work. -/
theorem exitWeightedFlatten_thenSkipIf_false {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten body source result price) :
    ExitWeightedFlatten (.ite cmp reg operand .skip body) source result
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  apply exitWeightedFlatten_thenSkipIf_transport body nonSkip cmp reg operand source x y lhs rhs false chosen
  apply exitWeightedFlatten_skipIf_true body nonSkip _ reg operand source x y lhs rhs _ price result bodyBound
  rw [Prelude.wordCmpNegate, chosen]
  rfl

/-- A false guard executes the nonempty else arm, charging its actual work. -/
theorem terminalWeightedFlatten_thenSkipIf_false {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten body source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand .skip body) source result outcome
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  apply terminalWeightedFlatten_thenSkipIf_transport body nonSkip cmp reg operand source x y lhs rhs false chosen
  apply terminalWeightedFlatten_skipIf_true body nonSkip _ reg operand source x y lhs rhs _ price result outcome bodyBound
  rw [Prelude.wordCmpNegate, chosen]
  rfl

/-- When both arms are empty the compiler emits no branch at all. Successful
operand evaluation therefore contributes zero native instructions. -/
theorem normalWeightedFlatten_bothSkipIf {F : Type}
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : Bool) (condition : wordSemWordCmp cmp x y = some chosen) :
    NormalWeightedFlatten (.ite cmp reg operand .skip .skip) source (fun _ _ => 0) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, _, _, _⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  dsimp only at evaluated
  rw [condition] at evaluated
  have same : post = source := by
    cases chosen <;> simpa only [StackSemEvaluate.evaluate_skip, Prod.mk.injEq, true_and] using evaluated.symm
  subst post
  refine ⟨start, 0, 0, related, ?_, rfl, Nat.le_refl _, ?_⟩
  · simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL,
      Flapjack.Compiler.Backend.StackToLab.stackIsSkip, appListAppend, appendAux]
  · simpa only [Nat.add_zero] using LabToTarget.WeightedMixedTrace.nil (code := encoded) start

#print axioms normalWeightedFlatten_bothSkipIf
#print axioms weighted_thenSkipIf_flatten
#print axioms weighted_thenSkipIf_evaluate
#print axioms normalWeightedFlatten_thenSkipIf_true
#print axioms normalWeightedFlatten_thenSkipIf_false
#print axioms exitWeightedFlatten_thenSkipIf_false
#print axioms terminalWeightedFlatten_thenSkipIf_false
end InitECandidate.Runtime.StackToLab
