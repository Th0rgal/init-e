import InitECandidate.Runtime.ArithmeticOpcodeSource
import InitECandidate.Runtime.GlobalKeepAllProgram
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def arithmeticHelperBody : ArithmeticOpcodeKind→ProgHOL 64
 | .add=>sourceFunctionBody Guest.guestFn_u256_add
 | .sub=>sourceFunctionBody Guest.guestFn_u256_sub
 | .mul=>sourceFunctionBody Guest.guestFn_u256_mul

theorem arithmetic_helper_original_lookup (kind : ArithmeticOpcodeKind) :
 originalRuntimeCode.lookup (arithmeticOpcodeHelper kind)=some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],arithmeticHelperBody kind,.comb [.one,.one,.one,.one]) := by
 cases kind with
 | add=>exact vmLookup_u256_add
 | sub=>exact vmLookup_u256_sub
 | mul=>exact vmLookup_u256_mul
/-- Every real helper body in this finite original family is read-only at all
clocks and all results; this is checked against the installed source closure. -/
theorem arithmetic_helper_memory_frame (kind : ArithmeticOpcodeKind) : MemoryFrame (arithmeticHelperBody kind) := by
 cases kind with
 | add=>exact memoryFrame_of_good vmLookup_u256_add (by decide) (by decide)
 | sub=>exact memoryFrame_of_good vmLookup_u256_sub (by decide) (by decide)
 | mul=>exact memoryFrame_of_good vmLookup_u256_mul (by decide) (by decide)
#print axioms arithmetic_helper_original_lookup
#print axioms arithmetic_helper_memory_frame
end InitECandidate.Runtime
