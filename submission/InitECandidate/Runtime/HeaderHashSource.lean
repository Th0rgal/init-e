import InitECandidate.Runtime.EncodeHeaderSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
set_option maxRecDepth 100000
def headerHashAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_header_hash)
#print axioms source_run_attempt_headers_call
end InitECandidate.Runtime
