import InitECandidate.Runtime.EncPutU256GD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- The original RLP and transaction minimal-uint writers have identical
 source bodies; the actual RLP lookup and runtime remain separate. -/
theorem source_rlp_put_u256_puBody : sourceFunctionBody Guest.guestFn_rlp_put_u256=puBody := by
 rw [sourceFunctionBody_eq_structural]
 rfl
#print axioms source_rlp_put_u256_puBody
end InitECandidate.Runtime
