import InitECandidate.Runtime.GuestCostOpAdd
import InitECandidate.Runtime.PanShapeLookup
import InitECandidate.Runtime.PanNoArgsShapeLookup
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.OriginalArithmeticAddCode
import InitECandidate.Runtime.OriginalStackPushInstalled
import InitECandidate.Runtime.VmFn_stack_pop
import InitECandidate.Runtime.VmFn_charge_gas
import InitECandidate.Runtime.VmFn_u256_add
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

set_option maxHeartbeats 4000000

/-- The four-word value shape of a stack word tuple. -/
noncomputable def fourWordValue (w0 w1 w2 w3 : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]

/-- Any four-word tuple has the `comb4` shape. -/
theorem fourWordValue_shape (w0 w1 w2 w3 : BitVec 64) :
    shapeEqHOL comb4Shape (shapeOfHOLExact (fourWordValue w0 w1 w2 w3)) = true := by
  simp [fourWordValue, comb4Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]

/-- The installed `stack_pop` declaration: zero arguments, four-word return. -/
theorem opAdd_stackPop_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup) :
    lookupCodeHOLFinite code (ofString "stack_pop") [] =
      some (sourceFunctionBody Guest.guestFn_stack_pop, HolFiniteMapExact.empty, comb4Shape) := by
  have entry : code (ofString "stack_pop") =
      some ([], sourceFunctionBody Guest.guestFn_stack_pop, .comb [.one, .one, .one, .one]) := by
    rw [installed]
    exact vmLookup_stack_pop
  have := pan_no_args_shape_lookup code (ofString "stack_pop")
    (sourceFunctionBody Guest.guestFn_stack_pop) (.comb [.one, .one, .one, .one]) entry
  simpa [comb4Shape] using this

/-- The installed `charge_gas` declaration: one word argument, word return. -/
theorem opAdd_chargeGas_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup) (amount : BitVec 64) :
    lookupCodeHOLFinite code (ofString "charge_gas") [.val (.word amount)] =
      some (sourceFunctionBody Guest.guestFn_charge_gas,
        HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount)), .one) := by
  have entry : code (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFunctionBody Guest.guestFn_charge_gas, .one) := by
    rw [installed]
    exact vmLookup_charge_gas
  exact pan_single_word_lookup code (ofString "charge_gas") (ofString "amount")
    (sourceFunctionBody Guest.guestFn_charge_gas) amount entry

/-- The installed `u256_add` declaration: two four-word arguments, four-word return. -/
theorem opAdd_u256Add_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup)
    (vx vy : ValueHOL 64)
    (hx : shapeEqHOL comb4Shape (shapeOfHOLExact vx) = true)
    (hy : shapeEqHOL comb4Shape (shapeOfHOLExact vy) = true) :
    lookupCodeHOLFinite code (ofString "u256_add") [vx, vy] =
      some (sourceFunctionBody Guest.guestFn_u256_add,
        (HolFiniteMapExact.empty.update (ofString "a", vx)).update (ofString "b", vy),
        comb4Shape) := by
  have entry : code (ofString "u256_add") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
        (ofString "b", .comb [.one, .one, .one, .one])],
        sourceFunctionBody Guest.guestFn_u256_add, .comb [.one, .one, .one, .one]) := by
    rw [installed]
    exact vmLookup_u256_add
  have different : (ofString "a" : MlS) ≠ ofString "b" := by decide_cbv
  have := pan_two_shape_lookup code (ofString "u256_add") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_u256_add) (.comb [.one, .one, .one, .one])
    (.comb [.one, .one, .one, .one]) (.comb [.one, .one, .one, .one]) vx vy
    different entry (by simpa [comb4Shape] using hx) (by simpa [comb4Shape] using hy)
  simpa [comb4Shape] using this

/-- The installed `stack_push` declaration: one four-word argument, word return. -/
theorem opAdd_stackPush_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup)
    (v : ValueHOL 64) (hv : shapeEqHOL comb4Shape (shapeOfHOLExact v) = true) :
    lookupCodeHOLFinite code (ofString "stack_push") [v] =
      some (sourceFunctionBody Guest.guestFn_stack_push,
        HolFiniteMapExact.empty.update (ofString "v", v), .one) := by
  have entry : code (ofString "stack_push") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFunctionBody Guest.guestFn_stack_push, .one) := by
    rw [installed]
    exact originalRuntimeCode_stackPush_lookup
  have := pan_single_shape_lookup code (ofString "stack_push") (ofString "v")
    (sourceFunctionBody Guest.guestFn_stack_push) (.comb [.one, .one, .one, .one]) .one v
    entry (by simpa [comb4Shape] using hv)
  simpa [comb4Shape] using this

/-- The installed `pc_add` declaration: one word argument, word return. -/
theorem opAdd_pcAdd_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup) (n : BitVec 64) :
    lookupCodeHOLFinite code (ofString "pc_add") [.val (.word n)] =
      some (sourceFunctionBody Guest.guestFn_pc_add,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word n)), .one) := by
  have entry : code (ofString "pc_add") =
      some ([(ofString "n", .one)], sourceFunctionBody Guest.guestFn_pc_add, .one) := by
    rw [installed]
    exact vmLookup_pc_add
  exact pan_single_word_lookup code (ofString "pc_add") (ofString "n")
    (sourceFunctionBody Guest.guestFn_pc_add) n entry

#print axioms fourWordValue_shape
#print axioms opAdd_stackPop_lookup
#print axioms opAdd_chargeGas_lookup
#print axioms opAdd_u256Add_lookup
#print axioms opAdd_stackPush_lookup
#print axioms opAdd_pcAdd_lookup
end InitECandidate.Runtime.FineCost
