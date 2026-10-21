import InitECandidate.Proofs.BackendStages.Padded597

namespace InitECandidate.Runtime.NativePadding

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Proofs.BackendStages

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Recorded span check: the recorded length of a line exceeds its own byte
length by at most `b`.  Labels carry no bytes and are accepted. -/
def padSlackOK {width : Nat} [NeZero width] (b : Nat)
    (line : LabSem.LabLineHOL width) : Bool :=
  match line with
  | .label _ _ _ => true
  | .asm _ bytes len => decide (len ≤ bytes.length + b)
  | .labAsm _ _ bytes len => decide (len ≤ bytes.length + b)

/-- One real chunk of the artifact: the first 64 lines of section 597 all have
recorded span within one four-byte chunk of their bytes. -/
theorem Padded597_chunk0 :
    (Padded597.lines.take 64).all (padSlackOK (width := 64) 4) = true := by
  decide_cbv

end InitECandidate.Runtime.NativePadding
#print axioms InitECandidate.Runtime.NativePadding.Padded597_chunk0
