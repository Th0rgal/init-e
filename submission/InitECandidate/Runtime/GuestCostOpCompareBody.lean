import InitECandidate.Runtime.GuestCostOpPopBody
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 4000000

/-- Actual `op_lt` body: pop x, pop y, charge three gas, compute `u256_lt`,
push the boolean, advance pc and return. -/
theorem source_opLt_body :
    sourceFunctionBody Guest.guestFn_op_lt =
      .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
        (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.const (3 : BitVec 64)])
            (.decCall (ofString "r") .one (ofString "u256_lt")
              [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")]
              (.seq (.call (some (none, none)) (ofString "stack_push_bool")
                  [.var VarKind.local (ofString "r")])
                (.seq (.call (some (none, none)) (ofString "pc_add")
                    [.const (1 : BitVec 64)])
                  (.return (.const (0 : BitVec 64)))))))) := by
  cbv

/-- Actual `op_gt` body: same shape with `u256_gt`. -/
theorem source_opGt_body :
    sourceFunctionBody Guest.guestFn_op_gt =
      .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
        (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.const (3 : BitVec 64)])
            (.decCall (ofString "r") .one (ofString "u256_gt")
              [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")]
              (.seq (.call (some (none, none)) (ofString "stack_push_bool")
                  [.var VarKind.local (ofString "r")])
                (.seq (.call (some (none, none)) (ofString "pc_add")
                    [.const (1 : BitVec 64)])
                  (.return (.const (0 : BitVec 64)))))))) := by
  cbv

/-- `u256_gt` is the swapped-argument `u256_lt`. -/
theorem source_u256Gt_body :
    sourceFunctionBody Guest.guestFn_u256_gt =
      .call none (ofString "u256_lt")
        [.var VarKind.local (ofString "b"), .var VarKind.local (ofString "a")] := by
  cbv

/-- Actual `stack_push_bool` body: nonzero means one, zero means zero. -/
theorem source_stackPushBool_body :
    sourceFunctionBody Guest.guestFn_stack_push_bool =
      .seq
        (.ite (.cmp Cmp.notEqual (.var VarKind.local (ofString "b")) (.const (0 : BitVec 64)))
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const (1 : BitVec 64), .const (0 : BitVec 64),
              .const (0 : BitVec 64), .const (0 : BitVec 64)]])
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const (0 : BitVec 64), .const (0 : BitVec 64),
              .const (0 : BitVec 64), .const (0 : BitVec 64)]]))
        (.return (.const (0 : BitVec 64))) := by
  cbv

#print axioms source_u256Gt_body
#print axioms source_stackPushBool_body

/-- One comparison limb: if the limbs differ, return 1 when `a` is lower, else 0. -/
def u256LtLimb (index : Nat) : ProgHOL 64 :=
  .ite (.cmp Cmp.notEqual (.rfield index (.var VarKind.local (ofString "a")))
      (.rfield index (.var VarKind.local (ofString "b"))))
    (.seq (.ite (.cmp Cmp.lower (.rfield index (.var VarKind.local (ofString "a")))
          (.rfield index (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip)
      (.return (.const (0 : BitVec 64))))
    .skip

/-- The final limb is compared directly because a tie returns zero. -/
def u256LtFinal : ProgHOL 64 :=
  .ite (.cmp Cmp.lower (.rfield 0 (.var VarKind.local (ofString "a")))
      (.rfield 0 (.var VarKind.local (ofString "b"))))
    (.return (.const (1 : BitVec 64))) .skip

/-- The actual `u256_lt` body: compare limbs 3 down to 0, first difference decides. -/
theorem source_u256Lt_body :
    sourceFunctionBody Guest.guestFn_u256_lt =
      .seq (u256LtLimb 3) (.seq (u256LtLimb 2) (.seq (u256LtLimb 1)
        (.seq u256LtFinal (.return (.const (0 : BitVec 64)))))) := by
  unfold u256LtLimb u256LtFinal
  cbv

#print axioms source_u256Lt_body

#print axioms source_opLt_body
#print axioms source_opGt_body
end InitECandidate.Runtime.FineCost
