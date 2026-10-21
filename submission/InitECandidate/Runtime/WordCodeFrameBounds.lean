import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
namespace InitECandidate.Runtime.WordToStack
open Flapjack

/-- Code-wide frame eligibility states both coverage and size. A mere bound
on successful frame lookups is insufficient because codeRel uses getD. -/
def CodeFramesBounded {α : Type} (code : Spt α) (frames : Spt Nat) (limit : Nat) : Prop :=
  ∀ key body, sptLookup key code = some body →
    ∃ frame, sptLookup key frames = some frame ∧ frame ≤ limit

/-- Recover the actual compiled frame bound from the compiler's defaulted
frame relation, using a declaration for the reached code key. -/
theorem CodeFramesBounded.compiledFrame_le {α : Type} {code : Spt α}
    {frames : Spt Nat} {limit key compiledFrame : Nat} {body : α}
    (covered : CodeFramesBounded code frames limit)
    (found : sptLookup key code = some body)
    (related : (sptLookup key frames).getD compiledFrame = compiledFrame) :
    compiledFrame ≤ limit := by
  obtain ⟨frame, declared, small⟩ := covered key body found
  rw [declared] at related
  simp only [Option.getD_some] at related
  exact related ▸ small

/-- Ordinary state updates may transport eligibility by equality of the
code and frame maps; no heap, locals, or stack disjointness is required. -/
theorem CodeFramesBounded.transport {α : Type} {code code' : Spt α}
    {frames frames' : Spt Nat} {limit : Nat}
    (covered : CodeFramesBounded code frames limit)
    (sameCode : code'=code) (sameFrames : frames'=frames) :
    CodeFramesBounded code' frames' limit := by
  subst code'
  subst frames'
  exact covered

#print axioms CodeFramesBounded.compiledFrame_le
#print axioms CodeFramesBounded.transport
end InitECandidate.Runtime.WordToStack
