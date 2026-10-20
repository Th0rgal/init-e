import InitECandidate.Runtime.DivisionOpcodeSource
import InitECandidate.Runtime.VmFn_u256_div
import InitECandidate.Runtime.VmFn_u256_sdiv
import InitECandidate.Runtime.VmFn_u256_mod
import InitECandidate.Runtime.VmFn_u256_smod
import InitECandidate.Runtime.GlobalKeepAllProgram
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- The real division helper bodies, one per division opcode. -/
def divisionHelperBody : DivisionOpcodeKind→ProgHOL 64
 | .div=>sourceFunctionBody Guest.guestFn_u256_div
 | .sdiv=>sourceFunctionBody Guest.guestFn_u256_sdiv
 | .mod=>sourceFunctionBody Guest.guestFn_u256_mod
 | .smod=>sourceFunctionBody Guest.guestFn_u256_smod

/-- Globals frame of the real division helper bodies. Unlike `goodMem`, the
kernel-checked globals-keeping set `goodGA` does contain all four division
helpers, so their globals are preserved at every clock and every outcome. -/
theorem division_helper_globals_frame (kind : DivisionOpcodeKind) :
 ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code=originalRuntimeCode →
  (evaluateHOLFiniteState state (divisionHelperBody kind)).2.globals=state.globals := by
 cases kind with
 | div=>exact fun state code => evaluate_keepsGA goodGA goodGA_bodies (divisionHelperBody .div) (keepsGA_of_installed vmLookup_u256_div (by decide)) state code
 | sdiv=>exact fun state code => evaluate_keepsGA goodGA goodGA_bodies (divisionHelperBody .sdiv) (keepsGA_of_installed vmLookup_u256_sdiv (by decide)) state code
 | mod=>exact fun state code => evaluate_keepsGA goodGA goodGA_bodies (divisionHelperBody .mod) (keepsGA_of_installed vmLookup_u256_mod (by decide)) state code
 | smod=>exact fun state code => evaluate_keepsGA goodGA goodGA_bodies (divisionHelperBody .smod) (keepsGA_of_installed vmLookup_u256_smod (by decide)) state code
#print axioms division_helper_globals_frame
end InitECandidate.Runtime
