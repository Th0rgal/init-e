import InitECandidate.Runtime.WordStackReturningMotive
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- The original return convention and variable/frame bound cover all
spilled return slots; no independent return-count restriction is needed. -/
theorem returningReturnCount_le_frame {F : Type} (ac : AsmConfigExact 64) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.call (some (values,names,retCode,l1,l2)) dest args none) = true)
    (maximum : maxVarHOL (.call (some (values,names,retCode,l1,l2)) dest args none) < 2*frame+2*k) :
    Compiler.Backend.WordToStack.numStackRet k values ≤ f := by
  have positive := positiveCallerFrame k frame values names retCode l1 l2 dest args
    source xs args1 prog ss envs guards conventions maximum
  have shape : if frame = 0 then f = 0 else f = frame+1 := by
    unfold stateRel at related
    aesop (config := { enableSimp := false })
  rw [if_neg (by omega)] at shape
  have valuesEq := (returningConventions k values names retCode l1 l2 dest args conventions).2.2.1
  have valuesBound : values.length ≤ frame+k := by
    rcases Nat.eq_zero_or_pos values.length with empty | nonempty
    · omega
    · have member : 2 * ((values.length-1)+1) ∈ values := by
        have mapped : 2 * ((values.length-1)+1) ∈
            (List.range values.length).map (fun index => 2*(index+1)) :=
          List.mem_map.mpr ⟨values.length-1, List.mem_range.mpr (by omega), rfl⟩
        rwa [← valuesEq] at mapped
      have upper := maxList_ge_of_mem values _ member
      rw [maxVarHOL] at maximum
      simp only [Flapjack.WordAlloc.max3Eq] at maximum
      omega
  unfold Compiler.Backend.WordToStack.numStackRet
  omega

#print axioms returningReturnCount_le_frame
end InitECandidate.Runtime.WordToStack.ExecutedReturning
