import InitECandidate.Runtime.RawCallRefinedLocalPrice
import InitECandidate.Runtime.StackEmptyInstallOracle

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Static frame conditions used by the raw-call cost proof. A release must
be nonempty; both allocations and releases fit one native frame chunk. -/
def rawCallFramesSupported : HolProg 64 → Bool
  | .stackFree count => decide (0 < count ∧ count ≤ 255)
  | .stackAlloc count => decide (count ≤ 255)
  | .seq first second | .ite _ _ _ first second =>
      rawCallFramesSupported first && rawCallFramesSupported second
  | .loop body => rawCallFramesSupported body
  | .call (some (body, _, _, _)) _ handler => rawCallFramesSupported body &&
      (match handler with | none => true | some (hp, _, _) => rawCallFramesSupported hp)
  | _ => true
termination_by p => sizeOf p

def rawCallCodeFramesSupported (code : List (Nat × HolProg 64)) : Bool :=
  code.all (fun entry => rawCallFramesSupported entry.2)

theorem rawCallCodeFramesSupported_append (a b : List (Nat × HolProg 64)) :
    rawCallCodeFramesSupported (a ++ b) =
      (rawCallCodeFramesSupported a && rawCallCodeFramesSupported b) := by
  simp [rawCallCodeFramesSupported]

theorem rawCallFramesSupported_free (count : Nat)
    (eligible : rawCallFramesSupported (.stackFree count) = true) :
    0 < count ∧ count ≤ 255 := by simpa [rawCallFramesSupported] using eligible

/-- Lookup form needed when entering an actually selected callee. -/
def RawCallFramesSupportedCode (code : Spt (HolProg 64)) : Prop :=
  ∀ key p, sptLookup key code = some p → rawCallFramesSupported p = true

theorem RawCallFramesSupportedCode.of_list (code : List (Nat × HolProg 64))
    (checked : rawCallCodeFramesSupported code = true) :
    RawCallFramesSupportedCode (sptFromAList code) := by
  intro key p found
  rw [sptLookup_sptFromAList] at found
  exact List.all_eq_true.mp checked (key, p) (sptAListLookup_mem _ _ _ found)

/-- The finite certificate survives reached executions when installation is
disabled by the actual oracle; no target cost premise is involved. -/
theorem RawCallFramesSupportedCode.after_evaluate {C F : Type} (p : HolProg 64)
    (source post : StackSemStateFiniteExact 64 C F) result
    (oracle : StackToLab.EmptyInstallOracle source)
    (eligible : RawCallFramesSupportedCode source.code)
    (run : StackSemEvaluate.evaluate (p, source) = (result, post)) :
    RawCallFramesSupportedCode post.code ∧ StackToLab.EmptyInstallOracle post := by
  obtain ⟨code, postOracle⟩ := StackToLab.evaluate_emptyInstallOracle
    p source post result oracle run
  exact ⟨code ▸ eligible, postOracle⟩

#print axioms rawCallCodeFramesSupported_append
#print axioms rawCallFramesSupported_free
#print axioms RawCallFramesSupportedCode.of_list
#print axioms RawCallFramesSupportedCode.after_evaluate
end InitECandidate.Runtime.StackRawCall
