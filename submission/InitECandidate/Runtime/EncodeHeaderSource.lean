import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
set_option maxRecDepth 100000
def encodeHeaderAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_encode_header)
#print axioms source_run_attempt_headers_call
end InitECandidate.Runtime
