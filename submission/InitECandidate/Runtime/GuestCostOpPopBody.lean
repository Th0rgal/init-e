import InitECandidate.Runtime.GuestCostStackPop
import InitECandidate.Runtime.GuestCostChargeFamily
import InitECandidate.Runtime.GuestCostPcAdd
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- The actual `op_pop` source body: pop one U256, charge two gas, advance pc, return. -/
theorem source_opPop_body :
    sourceFunctionBody Guest.guestFn_op_pop =
      .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
        (.seq (.call (some (none, none)) (ofString "charge_gas")
            [.const (2 : BitVec 64)])
          (.seq (.call (some (none, none)) (ofString "pc_add")
              [.const (1 : BitVec 64)])
            (.return (.const (0 : BitVec 64))))) := by
  cbv

#print axioms source_opPop_body
end InitECandidate.Runtime.FineCost
