import Flapjack.Compiler.Backend.StackLang.Prog
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- All syntactic callees are direct and avoid the excluded label. Return
and exception continuations are checked too; unreachable stored code need
not be assigned a runtime price merely because it is installed. -/
def directCallsAvoid (forbidden : Nat) : HolProg 64 → Bool
  | .seq first second | .ite _ _ _ first second => directCallsAvoid forbidden first && directCallsAvoid forbidden second
  | .loop body => directCallsAvoid forbidden body
  | .rawCall label | .jumpLower _ _ label => decide (label ≠ forbidden)
  | .call ret dest handler =>
      (match dest with | .inl label => decide (label ≠ forbidden) | .inr _ => false) &&
      (match ret with | none => true | some (body, _, _, _) => directCallsAvoid forbidden body) &&
      (match handler with | none => true | some (body, _, _) => directCallsAvoid forbidden body)
  | _ => true
termination_by p => sizeOf p

theorem directCallsAvoid_direct {ret dest handler forbidden}
    (checked : directCallsAvoid forbidden (.call ret dest handler) = true) :
    ∃ label, dest = Sum.inl label ∧ label ≠ forbidden := by
  cases ret with
  | none =>
    cases handler with
    | none => cases dest <;> simp_all [directCallsAvoid]
    | some packet =>
      rcases packet with ⟨body, hs, hl⟩
      cases dest <;> simp_all [directCallsAvoid]
  | some packet =>
    rcases packet with ⟨body, link, l1, l2⟩
    cases handler with
    | none => cases dest <;> simp_all [directCallsAvoid]
    | some packet =>
      rcases packet with ⟨hp, hs, hl⟩
      cases dest <;> simp_all [directCallsAvoid]

#print axioms directCallsAvoid_direct
end InitECandidate.Runtime.StackToLab
