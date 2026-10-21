import InitECandidate.Runtime.StackWeightedExit
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Loop
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Literal body installation used by every loop case. -/
def weightedLoopBodyLines (body : HolProg 64) (sectionId labelId : Nat)
    (continues breaks : List Nat) : List (LabLineHOL 64) :=
  appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId
    (labelId + 2) (labelId :: continues) ((labelId + 1) :: breaks)).1

def weightedLoopBodyLength (body : HolProg 64) (sectionId labelId : Nat)
    (continues breaks : List Nat) : Nat :=
  ((weightedLoopBodyLines body sectionId labelId continues breaks).filter
    (fun line => !isLabelHOL line)).length

/-- Shared layout geometry for final iterations, reentry, and propagated
exits. Labels have zero native length; the back jump is the one emitted line. -/
structure WeightedLoopLayout {F : Type} (body : HolProg 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) : Prop where
  bodyInstalled : codeInstalled start.pc (weightedLoopBodyLines body sectionId labelId continues breaks) start.code
  entry : locToPc sectionId labelId start.code = some start.pc
  back : asmFetchAux (start.pc + weightedLoopBodyLength body sectionId labelId continues breaks)
    start.code = some (.labAsm (.jump (.lab sectionId labelId)) 0 [] 0)
  exit : locToPc sectionId (labelId + 1) start.code =
    some (start.pc + weightedLoopBodyLength body sectionId labelId continues breaks + 1)
  labels : ∀ k ∈ (labelId :: continues) ++ ((labelId + 1) :: breaks) ++ [0],
    (locToPc sectionId k start.code).isSome
  length : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
    (.loop body) sectionId labelId continues breaks).1).filter (fun line => !isLabelHOL line)).length =
    weightedLoopBodyLength body sectionId labelId continues breaks + 1

theorem weightedLoopLayout_of_installed {F : Type}
    (body : HolProg 64) (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F)
    (installed : codeInstalled start.pc (appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.loop body) sectionId labelId continues breaks).1) start.code)
    (labels : ∀ k ∈ continues ++ breaks ++ [0], (locToPc sectionId k start.code).isSome) :
    WeightedLoopLayout body flag sectionId labelId continues breaks start := by
  have tf : Flapjack.Compiler.Backend.StackToLab.flattenHOL flag (.loop body)
      sectionId labelId continues breaks =
      Flapjack.Compiler.Backend.StackToLab.flattenHOL false (.loop body) sectionId labelId continues breaks := by
    cases flag
    · rfl
    · exact flattenTF (by simp [Flapjack.Compiler.Backend.StackToLab.isSeqHOL])
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId
      (labelId + 2) (labelId :: continues) ((labelId + 1) :: breaks) with ⟨xs, nr, next⟩
  have flat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.loop body) sectionId labelId continues breaks).1 =
      .label sectionId labelId 0 :: (appListAppend xs ++
        [.labAsm (.jump (.lab sectionId labelId)) 0 [] 0, .label sectionId (labelId + 1) 0]) := by
    rw [tf, Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    simp [h1, appListAppendAppend, appListAppendList]
  have total : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.loop body) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      ((appListAppend xs).filter (fun line => !isLabelHOL line)).length + 1 := by
    rw [flat]; simp [List.filter_append, isLabelHOL]
  rw [flat] at installed
  obtain ⟨locEntry, inst1⟩ := labelAt installed
  obtain ⟨instBody, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst1
  obtain ⟨fetchBack, instExit⟩ := lineAt rfl instRest
  obtain ⟨locExit, _⟩ := labelAt instExit
  have labelsBody : ∀ k ∈ (labelId :: continues) ++ ((labelId + 1) :: breaks) ++ [0],
      (locToPc sectionId k start.code).isSome := by
    intro k member
    by_cases first : k = labelId
    · subst first; simp [locEntry]
    by_cases last : k = labelId + 1
    · subst last; simp [locExit]
    apply labels k
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member ⊢
    tauto
  refine ⟨?_, locEntry, ?_, ?_, labelsBody, ?_⟩
  · simpa only [weightedLoopBodyLines, h1] using instBody
  · simpa only [weightedLoopBodyLength, weightedLoopBodyLines, h1] using fetchBack
  · simpa only [weightedLoopBodyLength, weightedLoopBodyLines, h1] using locExit
  · simpa only [weightedLoopBodyLength, weightedLoopBodyLines, h1] using total

#print axioms weightedLoopLayout_of_installed
end InitECandidate.Runtime.StackToLab
