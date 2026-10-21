import InitECandidate.Runtime.GuestWordFrameCoverage
import InitECandidate.Proofs.StackFrameComputation
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import Flapjack.Misc.Sptree.Map
import Flapjack.Misc.Sptree.MapiLookup
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs InitECandidate.Proofs.BackendStages

/-- The initialized semantic frame map is indexed over the exact source
code; coverage and bounds follow from its pointwise computed frame sizes. -/
theorem CodeFramesBounded.mapi {α : Type} (code : Spt α) (frame : Nat → α → Nat) (limit : Nat)
    (small : ∀ key value, sptLookup key code = some value → frame key value ≤ limit) :
    CodeFramesBounded code (sptMapi frame code) limit := by
  intro key value found
  refine ⟨frame key value,?_,small key value found⟩
  rw [sptLookupMapi,found]
  rfl

private theorem guest_frame_map_eq : Native.wordConfig.stackFrameSize =
    sptFromAList (Native.programs0.map (fun entry =>
      (entry.1,StackFrameComputation.frameSize 22 entry.2.1 entry.2.2))) := by
  have eq := StackFrameComputation.frameMap_eq riscvConfig false Native.programs0
  rw [Native.native_eq] at eq
  exact eq

/-- Actual Word initialization constructs the same bounded frame values as
the certified native compiler map, including total lookup coverage. -/
theorem guest_word_initialization_frames {C F : Type}
    (target : StackSemStateFiniteExact 64 C F)
    (oracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    let source := Compiler.Backend.WordToStack.Native.Initialization.makeInit riscvConfig 22 target
      (sptFromAList Native.programs0) oracle
    CodeFramesBounded source.code source.stackSize 92 := by
  apply CodeFramesBounded.mapi
  intro key value found
  change sptLookup key (sptFromAList Native.programs0) = some value at found
  let size : Nat × WordLangProgHOL (BitVec 64) → Nat := fun value =>
    StackFrameComputation.frameSize 22 value.1 value.2
  have mapped : sptLookup key (sptMap size (sptFromAList Native.programs0)) = some (size value) := by
    rw [sptLookup_sptMap,found]
    rfl
  rw [sptMap_sptFromAList] at mapped
  have actual : sptLookup key Native.wordConfig.stackFrameSize = some (size value) := by
    rw [guest_frame_map_eq]
    exact mapped
  have small := guest_word_frame_lookup_bound key (size value) actual
  exact small

#print axioms CodeFramesBounded.mapi
#print axioms guest_word_initialization_frames
end InitECandidate.Runtime.WordToStack
