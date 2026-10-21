import InitECandidate.Runtime.RawCallRefinedLocalPrice

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

#print axioms rawCallCodeFramesSupported_append
#print axioms rawCallFramesSupported_free
end InitECandidate.Runtime.StackRawCall
