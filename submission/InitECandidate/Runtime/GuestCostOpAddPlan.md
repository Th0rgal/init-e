# op_add dispatch coverage: what remains

`guestFn_op_add` (Guest/Ast.lean:12774) is the first real EVM opcode arm. Its
declared body is

```
decCall x comb4 "stack_pop" []
  (decCall y comb4 "stack_pop" []
    (seq (call (some (none, none)) "charge_gas" [.const 3])
      (decCall r comb4 "u256_add" [.var x, .var y]
        (seq (call (some (none, none)) "stack_push" [.var r])
          (seq (call (some (none, none)) "pc_add" [.const 1])
            (return (.const 0)))))))
```

Coverage requires a trace and an explicit price for each nested piece, then the
`declareCallReturn` composition (which now also charges the declared shape's
return-slot frame, epoch ddbe9047a) and finally the `.call` wrapper for the arm
from the dispatcher.

Pieces and their state:

| piece | body | status |
| --- | --- | --- |
| `charge_gas` call (`.const 3`) | `guestFn_charge_gas` | traced and priced: `chargeGas_body_run`, `chargeGasBodyEvents_score`, rejection prefix `chargeGas_outOfGas_run` |
| composition rules | - | `seq_statement_cost`, `ite_statement_cost`, `store_statement_cost`, `dec_statement_cost` |
| `stack_pop` declared call | `guestFn_stack_pop` (12295): dec `sp`, empty-stack `raise EvmErr 2` guard, then the pop path | not started |
| `u256_add` declared call | `guestFn_u256_add` (1057): four `PrimOp.addCarry` limbs over a comb4 pair | not started |
| `stack_push` call | `guestFn_stack_push` (12314): dec `sp`, dec `cap`, nested capacity `ite`s, memory write | not started |
| `pc_add` call | `guestFn_pc_add` (12686): one load/op/store on the `ev` frame and `return 0` | not started |

Interpreter-side obligations that come after the arm itself: the dispatch case
that emits this `.call`, the whole interpreter loop against the
invariant-aware `GasAmortizedBody` (allowed-state predicate `I`), and the
input-size term.

Known slack in what is already landed: the helper and family prices use a
16-statement over-count (safe upper bound, not sharp), and `charge_gas` call
cost still flows through `callLocalCost`.
