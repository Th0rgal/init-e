import InitECandidate.Runtime.SourceClock
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def statelessNext : ProgHOL 64 → ProgHOL 64
  | .dec _ _ _ body | .decCall _ _ _ _ body | .seq _ body => body
  | _ => .skip

def statelessAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_decode_stateless_input
  | n + 1 => statelessNext (statelessAt n)

end InitECandidate.Runtime
