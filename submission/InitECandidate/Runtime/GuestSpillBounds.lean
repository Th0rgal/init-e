import InitECandidate.Runtime.GuestRemovalEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Linear syntactic check of actual memory offsets and frame operations. -/
def spillBounds (slots frames : Nat) : HolProg 64 → Bool
  | .seq first second | .ite _ _ _ first second => spillBounds slots frames first && spillBounds slots frames second
  | .loop body => spillBounds slots frames body
  | .call ret _ handler =>
      (match ret with | none => true | some (body, _, _, _) => spillBounds slots frames body) &&
      (match handler with | none => true | some (body, _, _) => spillBounds slots frames body)
  | .stackLoad _ count | .stackStore _ count => decide (count ≤ slots)
  | .stackAlloc count | .stackFree count => decide (count ≤ frames)
  | _ => true
termination_by p => sizeOf p

/-- Every concrete guest spill fits a RISC-V immediate offset, and every
frame operation uses at most one 255-word allocation/release chunk. -/
theorem guest_spill_bounds :
    InitECandidate.Proofs.BackendStages.Alloc.bodies0.all (fun entry => spillBounds 91 92 entry.2) = true := by
  decide_cbv

#print axioms guest_spill_bounds
end InitECandidate.Runtime.StackToLab
