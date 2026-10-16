import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Full original WordToStack simulation motive with a retained clock ceiling. -/
def BoundedSimulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (budget : Nat := 0) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∃ (extraClock : Nat), extraClock ≤ budget ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens


theorem BoundedSimulation.mono {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {program : WordLangProgHOL (BitVec width)}
    {source : WordSemStateFiniteExact width (Nat × C) F} {a b : Nat}
    (simulation : BoundedSimulation ac program source a) (bound : a ≤ b) :
    BoundedSimulation ac program source b := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises
  obtain ⟨clock, le, final, targetResult, run, related⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises
  exact ⟨clock, Nat.le_trans le bound, final, targetResult, run, related⟩

theorem BoundedSimulation.forget {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {program : WordLangProgHOL (BitVec width)}
    {source : WordSemStateFiniteExact width (Nat × C) F} {budget : Nat}
    (simulation : BoundedSimulation ac program source budget) : Seq.Simulation ac program source := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises
  obtain ⟨clock, _, final, targetResult, run, related⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises
  exact ⟨clock, final, targetResult, run, related⟩

#print axioms BoundedSimulation.forget

end InitECandidate.Runtime.WordToStack
