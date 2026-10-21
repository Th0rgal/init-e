import Flapjack.Compiler.Backend.WordRemove.Proofs.CompileState
import Flapjack.Misc.Sptree.Map
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
set_option maxHeartbeats 3000000

/-- Preserve function labels and arities while compiling each body with its
actual arity. Unlike an arity-independent map, this supports full SSA setup. -/
def wordArityCodeMap {Source Target : Type} (transform : Nat → Source → Target)
    (code : Spt (Nat × Source)) : Spt (Nat × Target) :=
  sptMap (fun entry => (entry.1,transform entry.1 entry.2)) code

theorem wordArityCodeMap_lookup {Source Target : Type} (transform : Nat → Source → Target)
    (code : Spt (Nat × Source)) (label : Nat) :
    sptLookup label (wordArityCodeMap transform code) =
      (sptLookup label code).map (fun entry => (entry.1,transform entry.1 entry.2)) := by
  exact sptLookup_sptMap _ _ _

/-- Direct lookup passes the full argument list; indirect lookup drops the
function pointer. In either case the accepted arity is exactly the length of
the actual callee arguments, so setupSSA receives the correct count. -/
theorem wordArityCodeMap_findCode {width : Nat} [NeZero width]
    {Source Target StackSize : Type} (transform : Nat → Source → Target)
    (destination : Option Nat) (arguments : List (WordLocW width))
    (code : Spt (Nat × Source)) (sizes : Spt StackSize) :
    wordSemFindCode destination arguments (wordArityCodeMap transform code) sizes =
      (wordSemFindCode destination arguments code sizes).map
        (fun found => (found.1,transform found.1.length found.2.1,found.2.2)) := by
  cases destination with
  | some label =>
    simp only [wordSemFindCode,wordArityCodeMap_lookup]
    cases sptLookup label code with
    | none => rfl
    | some entry =>
      obtain ⟨arity,body⟩ := entry
      simp only [Option.map]
      split
      · rename_i accepted
        simp only [Option.map,accepted]
      · rfl
  | none =>
    simp only [wordSemFindCode]
    split
    · rfl
    · split
      · simp only [wordArityCodeMap_lookup]
        rename_i label _
        cases sptLookup label code with
        | none => rfl
        | some entry =>
          obtain ⟨arity,body⟩ := entry
          simp only [Option.map]
          split
          · rename_i accepted
            have actualArity : arguments.dropLast.length = arity := by
              rw [List.length_dropLast]
              omega
            simp only [Option.map,actualArity]
          · rfl
      · rfl

#print axioms wordArityCodeMap_lookup
#print axioms wordArityCodeMap_findCode
end InitECandidate.Runtime.FineCost
