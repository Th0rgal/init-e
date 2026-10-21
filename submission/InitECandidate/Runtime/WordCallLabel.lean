import InitECandidate.Runtime.WordArityCodeMap
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
set_option maxHeartbeats 2000000

/-- Function identity at a call, before callEnv discards the pointer argument.
This follows exactly the direct/indirect distinction in wordSemFindCode. -/
def wordCallLabel {width : Nat} [NeZero width] (destination : Option Nat)
    (arguments : List (WordLocW width)) : Option Nat :=
  match destination with
  | some label => some label
  | none =>
    if empty : arguments = [] then none
    else match arguments.getLast empty with
      | .loc label 0 => some label
      | _ => none

/-- A successful lookup resolves to a real label/arity in the source table.
The accepted arity is the actual callee argument count, including the dropped
indirect pointer. This supplies function identity for function-indexed costs. -/
theorem wordCallLabel_findCode {width : Nat} [NeZero width] {Code Size : Type}
    (destination : Option Nat) (arguments actualArguments : List (WordLocW width))
    (code : Spt (Nat × Code)) (sizes : Spt Size) (body : Code) (size : Option Size)
    (found : wordSemFindCode destination arguments code sizes = some (actualArguments,body,size)) :
    ∃ label, wordCallLabel destination arguments = some label ∧
      sptLookup label code = some (actualArguments.length,body) := by
  cases destination with
  | some label =>
    simp only [wordSemFindCode] at found
    cases lookup : sptLookup label code with
    | none => simp [lookup] at found
    | some pair =>
      rcases pair with ⟨arity,body'⟩
      rw [lookup] at found
      dsimp only at found
      split at found
      · rename_i accepted
        simp only [Option.some.injEq,Prod.mk.injEq] at found
        rcases found with ⟨rfl,rfl,rfl⟩
        exact ⟨label,rfl,by simpa only [accepted] using lookup⟩
      · cases found
  | none =>
    simp only [wordSemFindCode] at found
    split at found
    · cases found
    · rename_i nonempty
      split at found
      · rename_i label pointer
        cases lookup : sptLookup label code with
        | none => simp [lookup] at found
        | some pair =>
          rcases pair with ⟨arity,body'⟩
          rw [lookup] at found
          dsimp only at found
          split at found
          · rename_i accepted
            simp only [Option.some.injEq,Prod.mk.injEq] at found
            rcases found with ⟨rfl,rfl,rfl⟩
            have actualArity : arguments.dropLast.length = arity := by
              rw [List.length_dropLast]
              omega
            refine ⟨label,?_,?_⟩
            · simp only [wordCallLabel,dif_neg nonempty,if_neg nonempty,pointer]
            · simpa only [actualArity] using lookup
          · cases found
      · cases found

#print axioms wordCallLabel_findCode
end InitECandidate.Runtime.FineCost
