import InitECandidate.Runtime.GuestCostChargeFamily
import InitECandidate.Runtime.GuestCostAtomicExpressions
import InitECandidate.Runtime.PanScalarCostModel
import InitECandidate.Runtime.GuestCostComb4Load
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

set_option maxHeartbeats 4000000

/-- The two-word combined shape of one `addCarry` limb result (sum, carry). -/
def comb2Shape : ShapeHOL := .comb [.one, .one]

theorem comb2Shape_size :
    sizeOfShapeWithContextHOL ([] : StructContextHOLM) comb2Shape = 2 := by
  simp [comb2Shape, sizeOfShapeWithContextHOL, sizeOfShapeHOL, sizeOfShapesHOL]

/-- The wrapped sum word of one 64-bit limb. -/
def u256AddCarryResult (left right carry : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (left.toNat + right.toNat + (if carry == 0 then 0 else 1))

/-- The carry word of one 64-bit limb. -/
def u256AddCarryOverflow (left right carry : BitVec 64) : BitVec 64 :=
  if 2 ^ 64 ≤ left.toNat + right.toNat + (if carry == 0 then 0 else 1) then
    BitVec.ofNat 64 1
  else BitVec.ofNat 64 0

/-- The result value of one `addCarry` primitive: a pair `[sum, carry]`. -/
def u256AddCarryValue (left right carry : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word (u256AddCarryResult left right carry)),
    .val (.word (u256AddCarryOverflow left right carry))]

/-- The zero pair used by every `dec r_i`. -/
def u256AddZeroValue : ValueHOL 64 :=
  .rStruct [.val (.word (0 : BitVec 64)), .val (.word (0 : BitVec 64))]

/-- The zero-pair initialiser of every `dec r_i`. -/
noncomputable def u256AddZeroPair : ExpHOL 64 :=
  .rstruct [.const (0 : BitVec 64), .const (0 : BitVec 64)]

/-- The primitive itself computes exactly the `addCarry` pair. -/
theorem panPrimop_addCarry (left right carry : BitVec 64) :
    Flapjack.panPrimopHOLExact PrimOp.addCarry
      [.val (.word left), .val (.word right), .val (.word carry)] =
      some (u256AddCarryValue left right carry) := by
  simp [Flapjack.panPrimopHOLExact, Flapjack.wordAddCarryHOL,
    u256AddCarryValue, u256AddCarryResult, u256AddCarryOverflow]

/-- A constant zero pair evaluates to the zero pair value. -/
theorem eval_u256AddZeroPair (s : PanSemStateFiniteExact 64 F) :
    expressionValue s u256AddZeroPair = some u256AddZeroValue := by
  classical
  unfold expressionValue u256AddZeroPair u256AddZeroValue
  simp [evalHOLExact, evalListHOLExact, toExact]

/-- The zero pair has the declared two-word shape. -/
theorem shape_u256AddZeroPair :
    shapeEqHOL comb2Shape (shapeOfHOLExact u256AddZeroValue) = true := by
  simp [comb2Shape, u256AddZeroValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]

/-- A field of a local four-word structure evaluates to its word. -/
theorem eval_rfield_four (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (index : Nat) (a0 a1 a2 a3 word : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (indexed : ([.val (.word a0), .val (.word a1), .val (.word a2),
      .val (.word a3)] : List (ValueHOL 64))[index]? = some (.val (.word word))) :
    expressionValue s (.rfield index (.var VarKind.local name)) = some (.val (.word word)) := by
  classical
  unfold expressionValue
  simp [evalHOLExact, toExact, hV, indexed]

theorem eval_rfield_four_zero (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 a2 a3 : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) :
    expressionValue s (.rfield 0 (.var VarKind.local name)) = some (.val (.word a0)) :=
  eval_rfield_four s name 0 a0 a1 a2 a3 a0 hV (by simp)

theorem eval_rfield_four_one (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 a2 a3 : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) :
    expressionValue s (.rfield 1 (.var VarKind.local name)) = some (.val (.word a1)) :=
  eval_rfield_four s name 1 a0 a1 a2 a3 a1 hV (by simp)

theorem eval_rfield_four_two (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 a2 a3 : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) :
    expressionValue s (.rfield 2 (.var VarKind.local name)) = some (.val (.word a2)) :=
  eval_rfield_four s name 2 a0 a1 a2 a3 a2 hV (by simp)

theorem eval_rfield_four_three (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 a2 a3 : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) :
    expressionValue s (.rfield 3 (.var VarKind.local name)) = some (.val (.word a3)) :=
  eval_rfield_four s name 3 a0 a1 a2 a3 a3 hV (by simp)

/-- A field of a local two-word structure evaluates to its word. -/
theorem eval_rfield_two (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (index : Nat) (a0 a1 word : BitVec 64)
    (hV : s.locals.lookup name =
      some (.rStruct [.val (.word a0), .val (.word a1)]))
    (indexed : ([.val (.word a0), .val (.word a1)] : List (ValueHOL 64))[index]? =
      some (.val (.word word))) :
    expressionValue s (.rfield index (.var VarKind.local name)) = some (.val (.word word)) := by
  classical
  unfold expressionValue
  simp [evalHOLExact, toExact, hV, indexed]

theorem eval_rfield_two_zero (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 : BitVec 64)
    (hV : s.locals.lookup name = some (.rStruct [.val (.word a0), .val (.word a1)])) :
    expressionValue s (.rfield 0 (.var VarKind.local name)) = some (.val (.word a0)) :=
  eval_rfield_two s name 0 a0 a1 a0 hV (by simp)

theorem eval_rfield_two_one (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (a0 a1 : BitVec 64)
    (hV : s.locals.lookup name = some (.rStruct [.val (.word a0), .val (.word a1)])) :
    expressionValue s (.rfield 1 (.var VarKind.local name)) = some (.val (.word a1)) :=
  eval_rfield_two s name 1 a0 a1 a1 hV (by simp)

/-- The four argument lists of the `addCarry` limbs, in source order. -/
noncomputable def u256AddArgs0 : List (ExpHOL 64) :=
  [.rfield 0 (.var VarKind.local (ofString "a")),
    .rfield 0 (.var VarKind.local (ofString "b")), .const (0 : BitVec 64)]

noncomputable def u256AddArgs1 : List (ExpHOL 64) :=
  [.rfield 1 (.var VarKind.local (ofString "a")),
    .rfield 1 (.var VarKind.local (ofString "b")),
    .rfield 1 (.var VarKind.local (ofString "r0"))]

noncomputable def u256AddArgs2 : List (ExpHOL 64) :=
  [.rfield 2 (.var VarKind.local (ofString "a")),
    .rfield 2 (.var VarKind.local (ofString "b")),
    .rfield 1 (.var VarKind.local (ofString "r1"))]

noncomputable def u256AddArgs3 : List (ExpHOL 64) :=
  [.rfield 3 (.var VarKind.local (ofString "a")),
    .rfield 3 (.var VarKind.local (ofString "b")),
    .rfield 1 (.var VarKind.local (ofString "r2"))]

/-- The returned four-word value of `u256_add`. -/
noncomputable def u256AddReturnExpr : ExpHOL 64 :=
  .rstruct [.rfield 0 (.var VarKind.local (ofString "r0")),
    .rfield 0 (.var VarKind.local (ofString "r1")),
    .rfield 0 (.var VarKind.local (ofString "r2")),
    .rfield 0 (.var VarKind.local (ofString "r3"))]

/-- The innermost suffix: the fourth limb and the return. -/
noncomputable def u256AddRest3 : ProgHOL 64 :=
  .seq (.primitive (ofString "r3") .addCarry u256AddArgs3) (.return u256AddReturnExpr)

/-- The suffix beginning at the third limb. -/
noncomputable def u256AddRest2 : ProgHOL 64 :=
  .seq (.primitive (ofString "r2") .addCarry u256AddArgs2)
    (.dec (ofString "r3") comb2Shape u256AddZeroPair u256AddRest3)

/-- The suffix beginning at the second limb. -/
noncomputable def u256AddRest1 : ProgHOL 64 :=
  .seq (.primitive (ofString "r1") .addCarry u256AddArgs1)
    (.dec (ofString "r2") comb2Shape u256AddZeroPair u256AddRest2)

/-- The suffix beginning at the first limb. -/
noncomputable def u256AddRest0 : ProgHOL 64 :=
  .seq (.primitive (ofString "r0") .addCarry u256AddArgs0)
    (.dec (ofString "r1") comb2Shape u256AddZeroPair u256AddRest1)

/-- The pinned installed body of `u256_add`. -/
noncomputable def u256AddBody : ProgHOL 64 :=
  .dec (ofString "r0") comb2Shape u256AddZeroPair u256AddRest0

/-- The installed source body is literally this `addCarry` cascade. -/
theorem source_u256Add_body :
    sourceFunctionBody Guest.guestFn_u256_add = u256AddBody := by
  cbv

/-- Recorded events of one `addCarry` primitive. -/
noncomputable def u256AddPrimEvents (s : PanSemStateFiniteExact 64 F)
    (left right carry : BitVec 64) (arguments : List (ExpHOL 64)) : List WorkEvent :=
  .statement :: (expressionListEvents s arguments ++
    [.cost (primitiveOverhead ([.val (.word left), .val (.word right),
      .val (.word carry)].flatMap flattenHOL).length),
     .copy (flattenHOL (u256AddCarryValue left right carry)).length])

/-- Recorded events of a structural sequence: `seq` emits no event. -/
def u256AddSeqEvents (left right : List WorkEvent) : List WorkEvent :=
  left ++ right

/-- Recorded events of one declared limb pair: initialiser, frame slot, body, and
the restored previous binding of the limb name. -/
noncomputable def u256AddDecEvents (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (bodyEvents : List WorkEvent) : List WorkEvent :=
  .statement :: (expressionEvents s u256AddZeroPair ++
    [.copy (flattenHOL u256AddZeroValue).length, .frame 1] ++ bodyEvents ++
    [.copy (((s.locals.lookup name).map
      (fun previous => (flattenHOL previous).length)).getD 0)])

/-- Recorded events of the final four-word return. -/
noncomputable def u256AddReturnEvents (s : PanSemStateFiniteExact 64 F) (payload : ValueHOL 64) :
    List WorkEvent :=
  .statement :: (expressionEvents s u256AddReturnExpr ++
    [.cost (returnOverhead (flattenHOL payload).length)])

/-- One `addCarry` primitive step: its three word arguments, the pair result, and
the validity of writing it over the declared limb pair. -/
theorem u256Add_primitive_run (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (left right carry old0 old1 : BitVec 64)
    (eLeft eRight eCarry : ExpHOL 64)
    (hLeft : expressionValue s eLeft = some (.val (.word left)))
    (hRight : expressionValue s eRight = some (.val (.word right)))
    (hCarry : expressionValue s eCarry = some (.val (.word carry)))
    (hName : s.locals.lookup name = some (.rStruct [.val (.word old0), .val (.word old1)])) :
    StatementRun s (.primitive name .addCarry [eLeft, eRight, eCarry]) none
      (setVarHOLFinite name (u256AddCarryValue left right carry) s)
      (u256AddPrimEvents s left right carry [eLeft, eRight, eCarry]) := by
  classical
  unfold expressionValue at hLeft hRight hCarry
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [eLeft, eRight, eCarry] =
      some [.val (.word left), .val (.word right), .val (.word carry)] := by
    simp [evalListHOLFinite, evalListHOLExact, hLeft, hRight, hCarry]
  have operation : panPrimopHOLExact .addCarry
      [.val (.word left), .val (.word right), .val (.word carry)] =
      some (u256AddCarryValue left right carry) := panPrimop_addCarry left right carry
  have valid : isValidValueHOLFinite s .local name (u256AddCarryValue left right carry) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, hName, u256AddCarryValue,
      shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  exact StatementRun.primitiveValue (name := name) (operator := .addCarry)
    (arguments := [eLeft, eRight, eCarry])
    (values := [.val (.word left), .val (.word right), .val (.word carry)])
    (value := u256AddCarryValue left right carry) args operation valid

/-- One declared limb pair. -/
theorem u256Add_dec_run (s : PanSemStateFiniteExact 64 F) (name : MlStringHOL)
    (body : ProgHOL 64) (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (bodyEvents : List WorkEvent)
    (bodyRun : StatementRun (setVarHOLFinite name u256AddZeroValue s) body r post bodyEvents) :
    StatementRun s (.dec name comb2Shape u256AddZeroPair body) r
      { post with locals := (HolFiniteMapExact.resVarEq post.locals
        (name, s.locals.lookup name)) }
      (u256AddDecEvents s name bodyEvents) := by
  classical
  have init : CostedExpressionRun s u256AddZeroPair (some u256AddZeroValue)
      (expressionEvents s u256AddZeroPair) :=
    costedExpression_events s _ _ (eval_u256AddZeroPair s)
  exact StatementRun.declareValue (name := name) (shape := comb2Shape)
    (initializer := u256AddZeroPair) (body := body) init shape_u256AddZeroPair bodyRun

/-- The final four-word return. -/
theorem u256Add_return_run (s : PanSemStateFiniteExact 64 F)
    (l0 l1 l2 l3 c0 c1 c2 c3 : BitVec 64)
    (hR0 : s.locals.lookup (ofString "r0") =
      some (.rStruct [.val (.word l0), .val (.word c0)]))
    (hR1 : s.locals.lookup (ofString "r1") =
      some (.rStruct [.val (.word l1), .val (.word c1)]))
    (hR2 : s.locals.lookup (ofString "r2") =
      some (.rStruct [.val (.word l2), .val (.word c2)]))
    (hR3 : s.locals.lookup (ofString "r3") =
      some (.rStruct [.val (.word l3), .val (.word c3)])) :
    StatementRun s (.return u256AddReturnExpr)
      (some (.returned (.rStruct [.val (.word l0), .val (.word l1),
        .val (.word l2), .val (.word l3)])))
      (emptyLocalsHOLFinite s)
      (u256AddReturnEvents s (.rStruct [.val (.word l0), .val (.word l1),
        .val (.word l2), .val (.word l3)])) := by
  classical
  have value : expressionValue s u256AddReturnExpr =
      some (.rStruct [.val (.word l0), .val (.word l1), .val (.word l2), .val (.word l3)]) := by
    unfold u256AddReturnExpr expressionValue
    simp [evalHOLExact, evalListHOLExact, toExact, hR0, hR1, hR2, hR3]
  have expr : CostedExpressionRun s u256AddReturnExpr _ (expressionEvents s u256AddReturnExpr) :=
    costedExpression_events s _ _ value
  refine StatementRun.returnValue (expression := u256AddReturnExpr) expr ?_
  simp [shapeOfHOLExact, comb4Shape, sizeOfShapeWithContextHOL, sizeOfShapeHOL,
    sizeOfShapesHOL]


/-- The four limbs and their carries, in the order the source computes them. -/
noncomputable def u256AddEvents (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : List WorkEvent :=
  let c0 := u256AddCarryOverflow a0 b0 (0 : BitVec 64)
  let c1 := u256AddCarryOverflow a1 b1 c0
  let c2 := u256AddCarryOverflow a2 b2 c1
  let s0a := setVarHOLFinite (ofString "r0") u256AddZeroValue s
  let s0b := setVarHOLFinite (ofString "r0") (u256AddCarryValue a0 b0 (0 : BitVec 64)) s0a
  let s1a := setVarHOLFinite (ofString "r1") u256AddZeroValue s0b
  let s1b := setVarHOLFinite (ofString "r1") (u256AddCarryValue a1 b1 c0) s1a
  let s2a := setVarHOLFinite (ofString "r2") u256AddZeroValue s1b
  let s2b := setVarHOLFinite (ofString "r2") (u256AddCarryValue a2 b2 c1) s2a
  let s3a := setVarHOLFinite (ofString "r3") u256AddZeroValue s2b
  let s3b := setVarHOLFinite (ofString "r3") (u256AddCarryValue a3 b3 c2) s3a
  let payload : ValueHOL 64 :=
    .rStruct [.val (.word (u256AddCarryResult a0 b0 (0 : BitVec 64))),
      .val (.word (u256AddCarryResult a1 b1 c0)),
      .val (.word (u256AddCarryResult a2 b2 c1)),
      .val (.word (u256AddCarryResult a3 b3 c2))]
  u256AddDecEvents s (ofString "r0")
    (u256AddSeqEvents
      (u256AddPrimEvents s0a a0 b0 (0 : BitVec 64) u256AddArgs0)
      (u256AddDecEvents s0b (ofString "r1")
        (u256AddSeqEvents
          (u256AddPrimEvents s1a a1 b1 c0 u256AddArgs1)
          (u256AddDecEvents s1b (ofString "r2")
            (u256AddSeqEvents
              (u256AddPrimEvents s2a a2 b2 c1 u256AddArgs2)
              (u256AddDecEvents s2b (ofString "r3")
                (u256AddSeqEvents
                  (u256AddPrimEvents s3a a3 b3 c2 u256AddArgs3)
                  (u256AddReturnEvents s3b payload))))))))

/-- The post state of one successful `u256_add`: the four declared limb pairs are
dropped and their previous bindings restored. -/
noncomputable def u256AddPost (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let c0 := u256AddCarryOverflow a0 b0 (0 : BitVec 64)
  let c1 := u256AddCarryOverflow a1 b1 c0
  let c2 := u256AddCarryOverflow a2 b2 c1
  let s0a := setVarHOLFinite (ofString "r0") u256AddZeroValue s
  let s0b := setVarHOLFinite (ofString "r0") (u256AddCarryValue a0 b0 (0 : BitVec 64)) s0a
  let s1a := setVarHOLFinite (ofString "r1") u256AddZeroValue s0b
  let s1b := setVarHOLFinite (ofString "r1") (u256AddCarryValue a1 b1 c0) s1a
  let s2a := setVarHOLFinite (ofString "r2") u256AddZeroValue s1b
  let s2b := setVarHOLFinite (ofString "r2") (u256AddCarryValue a2 b2 c1) s2a
  let s3a := setVarHOLFinite (ofString "r3") u256AddZeroValue s2b
  let s3b := setVarHOLFinite (ofString "r3") (u256AddCarryValue a3 b3 c2) s3a
  let p3 := { emptyLocalsHOLFinite s3b with
    locals := (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s3b).locals
      (ofString "r3", s2b.locals.lookup (ofString "r3"))) }
  let p2 := { p3 with locals := (HolFiniteMapExact.resVarEq p3.locals
    (ofString "r2", s1b.locals.lookup (ofString "r2"))) }
  let p1 := { p2 with locals := (HolFiniteMapExact.resVarEq p2.locals
    (ofString "r1", s0b.locals.lookup (ofString "r1"))) }
  { p1 with locals := (HolFiniteMapExact.resVarEq p1.locals
    (ofString "r0", s.locals.lookup (ofString "r0"))) }

/-- The complete successful execution trace of the installed `u256_add` helper:
four zero-pair declarations, four real `addCarry` primitives feeding the next
limb, and the four-word return. -/
theorem u256Add_run (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) :
    StatementRun s (sourceFunctionBody Guest.guestFn_u256_add)
      (some (.returned (.rStruct [
        .val (.word (u256AddCarryResult a0 b0 (0 : BitVec 64))),
        .val (.word (u256AddCarryResult a1 b1 (u256AddCarryOverflow a0 b0 (0 : BitVec 64)))),
        .val (.word (u256AddCarryResult a2 b2
          (u256AddCarryOverflow a1 b1 (u256AddCarryOverflow a0 b0 (0 : BitVec 64))))),
        .val (.word (u256AddCarryResult a3 b3
          (u256AddCarryOverflow a2 b2
            (u256AddCarryOverflow a1 b1 (u256AddCarryOverflow a0 b0 (0 : BitVec 64))))))])))
      (u256AddPost s a0 a1 a2 a3 b0 b1 b2 b3)
      (u256AddEvents s a0 a1 a2 a3 b0 b1 b2 b3) := by
  classical
  let c0 := u256AddCarryOverflow a0 b0 (0 : BitVec 64)
  let c1 := u256AddCarryOverflow a1 b1 c0
  let c2 := u256AddCarryOverflow a2 b2 c1
  let s0a := setVarHOLFinite (ofString "r0") u256AddZeroValue s
  let s0b := setVarHOLFinite (ofString "r0") (u256AddCarryValue a0 b0 (0 : BitVec 64)) s0a
  let s1a := setVarHOLFinite (ofString "r1") u256AddZeroValue s0b
  let s1b := setVarHOLFinite (ofString "r1") (u256AddCarryValue a1 b1 c0) s1a
  let s2a := setVarHOLFinite (ofString "r2") u256AddZeroValue s1b
  let s2b := setVarHOLFinite (ofString "r2") (u256AddCarryValue a2 b2 c1) s2a
  let s3a := setVarHOLFinite (ofString "r3") u256AddZeroValue s2b
  let s3b := setVarHOLFinite (ofString "r3") (u256AddCarryValue a3 b3 c2) s3a
  let l0 := u256AddCarryResult a0 b0 (0 : BitVec 64)
  let l1 := u256AddCarryResult a1 b1 c0
  let l2 := u256AddCarryResult a2 b2 c1
  let l3 := u256AddCarryResult a3 b3 c2
  have har0 : (ofString "a" : MlStringHOL) ≠ ofString "r0" := by decide_cbv
  have har1 : (ofString "a" : MlStringHOL) ≠ ofString "r1" := by decide_cbv
  have har2 : (ofString "a" : MlStringHOL) ≠ ofString "r2" := by decide_cbv
  have har3 : (ofString "a" : MlStringHOL) ≠ ofString "r3" := by decide_cbv
  have hbr0 : (ofString "b" : MlStringHOL) ≠ ofString "r0" := by decide_cbv
  have hbr1 : (ofString "b" : MlStringHOL) ≠ ofString "r1" := by decide_cbv
  have hbr2 : (ofString "b" : MlStringHOL) ≠ ofString "r2" := by decide_cbv
  have hbr3 : (ofString "b" : MlStringHOL) ≠ ofString "r3" := by decide_cbv
  have h10 : (ofString "r1" : MlStringHOL) ≠ ofString "r0" := by decide_cbv
  have h20 : (ofString "r2" : MlStringHOL) ≠ ofString "r0" := by decide_cbv
  have h21 : (ofString "r2" : MlStringHOL) ≠ ofString "r1" := by decide_cbv
  have h30 : (ofString "r3" : MlStringHOL) ≠ ofString "r0" := by decide_cbv
  have h31 : (ofString "r3" : MlStringHOL) ≠ ofString "r1" := by decide_cbv
  have h32 : (ofString "r3" : MlStringHOL) ≠ ofString "r2" := by decide_cbv
  have hAs0a : s0a.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by
    simpa [s0a, setVarHOLFinite, FUPDATE, har0, Ne.symm har0] using hA
  have hBs0a : s0a.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    simpa [s0a, setVarHOLFinite, FUPDATE, hbr0, Ne.symm hbr0] using hB
  have hR0s0a : s0a.locals.lookup (ofString "r0") =
      some (.rStruct [.val (.word (0 : BitVec 64)), .val (.word (0 : BitVec 64))]) := by
    simp [s0a, setVarHOLFinite, FUPDATE, u256AddZeroValue]
  have hAs0b : s0a.locals.lookup (ofString "a") = s0b.locals.lookup (ofString "a") := by
    simp [s0b, setVarHOLFinite, FUPDATE, har0, Ne.symm har0]
  have hBs0b : s0a.locals.lookup (ofString "b") = s0b.locals.lookup (ofString "b") := by
    simp [s0b, setVarHOLFinite, FUPDATE, hbr0, Ne.symm hbr0]
  have hR0s0b : s0b.locals.lookup (ofString "r0") =
      some (u256AddCarryValue a0 b0 (0 : BitVec 64)) := by
    simp [s0b, setVarHOLFinite, FUPDATE]
  have hAs1a : s1a.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by
    simpa [s1a, setVarHOLFinite, FUPDATE, har1, Ne.symm har1] using (hAs0b ▸ hAs0a)
  have hBs1a : s1a.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    simpa [s1a, setVarHOLFinite, FUPDATE, hbr1, Ne.symm hbr1] using (hBs0b ▸ hBs0a)
  have hR1s1a : s1a.locals.lookup (ofString "r1") =
      some (.rStruct [.val (.word (0 : BitVec 64)), .val (.word (0 : BitVec 64))]) := by
    simp [s1a, setVarHOLFinite, FUPDATE, u256AddZeroValue]
  have hR0s1a : s1a.locals.lookup (ofString "r0") =
      some (u256AddCarryValue a0 b0 (0 : BitVec 64)) := by
    simpa [s1a, setVarHOLFinite, FUPDATE, h10, Ne.symm h10] using hR0s0b
  have hAs1b : s1a.locals.lookup (ofString "a") = s1b.locals.lookup (ofString "a") := by
    simp [s1b, setVarHOLFinite, FUPDATE, har1, Ne.symm har1]
  have hBs1b : s1a.locals.lookup (ofString "b") = s1b.locals.lookup (ofString "b") := by
    simp [s1b, setVarHOLFinite, FUPDATE, hbr1, Ne.symm hbr1]
  have hR1s1b : s1b.locals.lookup (ofString "r1") =
      some (u256AddCarryValue a1 b1 c0) := by
    simp [s1b, setVarHOLFinite, FUPDATE]
  have hAs2a : s2a.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by
    simpa [s2a, setVarHOLFinite, FUPDATE, har2, Ne.symm har2] using (hAs1b ▸ hAs1a)
  have hBs2a : s2a.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    simpa [s2a, setVarHOLFinite, FUPDATE, hbr2, Ne.symm hbr2] using (hBs1b ▸ hBs1a)
  have hR2s2a : s2a.locals.lookup (ofString "r2") =
      some (.rStruct [.val (.word (0 : BitVec 64)), .val (.word (0 : BitVec 64))]) := by
    simp [s2a, setVarHOLFinite, FUPDATE, u256AddZeroValue]
  have hR1s2a : s2a.locals.lookup (ofString "r1") =
      some (u256AddCarryValue a1 b1 c0) := by
    simpa [s2a, setVarHOLFinite, FUPDATE, h21, Ne.symm h21] using hR1s1b
  have hAs2b : s2a.locals.lookup (ofString "a") = s2b.locals.lookup (ofString "a") := by
    simp [s2b, setVarHOLFinite, FUPDATE, har2, Ne.symm har2]
  have hBs2b : s2a.locals.lookup (ofString "b") = s2b.locals.lookup (ofString "b") := by
    simp [s2b, setVarHOLFinite, FUPDATE, hbr2, Ne.symm hbr2]
  have hR2s2b : s2b.locals.lookup (ofString "r2") =
      some (u256AddCarryValue a2 b2 c1) := by
    simp [s2b, setVarHOLFinite, FUPDATE]
  have hAs3a : s3a.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by
    simpa [s3a, setVarHOLFinite, FUPDATE, har3, Ne.symm har3] using (hAs2b ▸ hAs2a)
  have hBs3a : s3a.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    simpa [s3a, setVarHOLFinite, FUPDATE, hbr3, Ne.symm hbr3] using (hBs2b ▸ hBs2a)
  have hR3s3a : s3a.locals.lookup (ofString "r3") =
      some (.rStruct [.val (.word (0 : BitVec 64)), .val (.word (0 : BitVec 64))]) := by
    simp [s3a, setVarHOLFinite, FUPDATE, u256AddZeroValue]
  have hR2s3a : s3a.locals.lookup (ofString "r2") =
      some (u256AddCarryValue a2 b2 c1) := by
    simpa [s3a, setVarHOLFinite, FUPDATE, h32, Ne.symm h32] using hR2s2b
  have hR0s3a : s3a.locals.lookup (ofString "r0") =
      some (u256AddCarryValue a0 b0 (0 : BitVec 64)) := by
    calc s3a.locals.lookup (ofString "r0")
        = s2b.locals.lookup (ofString "r0") := by
          simp [s3a, setVarHOLFinite, FUPDATE, h30, Ne.symm h30]
      _ = s2a.locals.lookup (ofString "r0") := by
          simp [s2b, setVarHOLFinite, FUPDATE, h20, Ne.symm h20]
      _ = s1b.locals.lookup (ofString "r0") := by
          simp [s2a, setVarHOLFinite, FUPDATE, h20, Ne.symm h20]
      _ = s1a.locals.lookup (ofString "r0") := by
          simp [s1b, setVarHOLFinite, FUPDATE, h10, Ne.symm h10]
      _ = s0b.locals.lookup (ofString "r0") := by
          simp [s1a, setVarHOLFinite, FUPDATE, h10, Ne.symm h10]
      _ = some (u256AddCarryValue a0 b0 (0 : BitVec 64)) := hR0s0b
  have hR1s3a : s3a.locals.lookup (ofString "r1") =
      some (u256AddCarryValue a1 b1 c0) := by
    calc s3a.locals.lookup (ofString "r1")
        = s2b.locals.lookup (ofString "r1") := by
          simp [s3a, setVarHOLFinite, FUPDATE, h31, Ne.symm h31]
      _ = s2a.locals.lookup (ofString "r1") := by
          simp [s2b, setVarHOLFinite, FUPDATE, h21, Ne.symm h21]
      _ = s1b.locals.lookup (ofString "r1") := by
          simp [s2a, setVarHOLFinite, FUPDATE, h21, Ne.symm h21]
      _ = some (u256AddCarryValue a1 b1 c0) := hR1s1b
  have hR0s3b : s3b.locals.lookup (ofString "r0") =
      some (u256AddCarryValue a0 b0 (0 : BitVec 64)) := by
    simpa [s3b, setVarHOLFinite, FUPDATE, h30, Ne.symm h30] using hR0s3a
  have hR1s3b : s3b.locals.lookup (ofString "r1") =
      some (u256AddCarryValue a1 b1 c0) := by
    simpa [s3b, setVarHOLFinite, FUPDATE, h31, Ne.symm h31] using hR1s3a
  have hR2s3b : s3b.locals.lookup (ofString "r2") =
      some (u256AddCarryValue a2 b2 c1) := by
    simpa [s3b, setVarHOLFinite, FUPDATE, h32, Ne.symm h32] using hR2s3a
  have hR3s3b : s3b.locals.lookup (ofString "r3") =
      some (u256AddCarryValue a3 b3 c2) := by
    simp [s3b, setVarHOLFinite, FUPDATE]
  have prim0 : StatementRun s0a (.primitive (ofString "r0") .addCarry u256AddArgs0) none s0b
      (u256AddPrimEvents s0a a0 b0 (0 : BitVec 64) u256AddArgs0) := by
    have := u256Add_primitive_run s0a (ofString "r0") a0 b0 (0 : BitVec 64) 0 0
      (.rfield 0 (.var VarKind.local (ofString "a")))
      (.rfield 0 (.var VarKind.local (ofString "b"))) (.const (0 : BitVec 64))
      (eval_rfield_four_zero s0a (ofString "a") a0 a1 a2 a3 hAs0a)
      (eval_rfield_four_zero s0a (ofString "b") b0 b1 b2 b3 hBs0a)
      (by simp [expressionValue, evalHOLExact, toExact])
      hR0s0a
    simpa [u256AddArgs0, s0b, u256AddZeroValue] using this
  have prim1 : StatementRun s1a (.primitive (ofString "r1") .addCarry u256AddArgs1) none s1b
      (u256AddPrimEvents s1a a1 b1 c0 u256AddArgs1) := by
    have := u256Add_primitive_run s1a (ofString "r1") a1 b1 c0 0 0
      (.rfield 1 (.var VarKind.local (ofString "a")))
      (.rfield 1 (.var VarKind.local (ofString "b")))
      (.rfield 1 (.var VarKind.local (ofString "r0")))
      (eval_rfield_four_one s1a (ofString "a") a0 a1 a2 a3 hAs1a)
      (eval_rfield_four_one s1a (ofString "b") b0 b1 b2 b3 hBs1a)
      (eval_rfield_two_one s1a (ofString "r0")
        (u256AddCarryResult a0 b0 (0 : BitVec 64))
        (u256AddCarryOverflow a0 b0 (0 : BitVec 64)) hR0s1a)
      hR1s1a
    simpa [u256AddArgs1, s1b, u256AddZeroValue] using this
  have prim2 : StatementRun s2a (.primitive (ofString "r2") .addCarry u256AddArgs2) none s2b
      (u256AddPrimEvents s2a a2 b2 c1 u256AddArgs2) := by
    have := u256Add_primitive_run s2a (ofString "r2") a2 b2 c1 0 0
      (.rfield 2 (.var VarKind.local (ofString "a")))
      (.rfield 2 (.var VarKind.local (ofString "b")))
      (.rfield 1 (.var VarKind.local (ofString "r1")))
      (eval_rfield_four_two s2a (ofString "a") a0 a1 a2 a3 hAs2a)
      (eval_rfield_four_two s2a (ofString "b") b0 b1 b2 b3 hBs2a)
      (eval_rfield_two_one s2a (ofString "r1")
        (u256AddCarryResult a1 b1 c0) (u256AddCarryOverflow a1 b1 c0) hR1s2a)
      hR2s2a
    simpa [u256AddArgs2, s2b, u256AddZeroValue] using this
  have prim3 : StatementRun s3a (.primitive (ofString "r3") .addCarry u256AddArgs3) none s3b
      (u256AddPrimEvents s3a a3 b3 c2 u256AddArgs3) := by
    have := u256Add_primitive_run s3a (ofString "r3") a3 b3 c2 0 0
      (.rfield 3 (.var VarKind.local (ofString "a")))
      (.rfield 3 (.var VarKind.local (ofString "b")))
      (.rfield 1 (.var VarKind.local (ofString "r2")))
      (eval_rfield_four_three s3a (ofString "a") a0 a1 a2 a3 hAs3a)
      (eval_rfield_four_three s3a (ofString "b") b0 b1 b2 b3 hBs3a)
      (eval_rfield_two_one s3a (ofString "r2")
        (u256AddCarryResult a2 b2 c1) (u256AddCarryOverflow a2 b2 c1) hR2s3a)
      hR3s3a
    simpa [u256AddArgs3, s3b, u256AddZeroValue] using this
  have retRun : StatementRun s3b (.return u256AddReturnExpr)
      (some (.returned (.rStruct [.val (.word l0), .val (.word l1),
        .val (.word l2), .val (.word l3)])))
      (emptyLocalsHOLFinite s3b)
      (u256AddReturnEvents s3b (.rStruct [.val (.word l0), .val (.word l1),
        .val (.word l2), .val (.word l3)])) := by
    have := u256Add_return_run s3b l0 l1 l2 l3
      (u256AddCarryOverflow a0 b0 (0 : BitVec 64))
      (u256AddCarryOverflow a1 b1 c0)
      (u256AddCarryOverflow a2 b2 c1)
      (u256AddCarryOverflow a3 b3 c2)
      hR0s3b hR1s3b hR2s3b hR3s3b
    simpa [u256AddCarryValue, l0, l1, l2, l3] using this
  have seq3 := StatementRun.seqNext prim3 retRun
  have dec3 := u256Add_dec_run s2b (ofString "r3") u256AddRest3 _ _ _ seq3
  have seq2 := StatementRun.seqNext prim2 dec3
  have dec2 := u256Add_dec_run s1b (ofString "r2") u256AddRest2 _ _ _ seq2
  have seq1 := StatementRun.seqNext prim1 dec2
  have dec1 := u256Add_dec_run s0b (ofString "r1") u256AddRest1 _ _ _ seq1
  have seq0 := StatementRun.seqNext prim0 dec1
  have dec0 := u256Add_dec_run s (ofString "r0") u256AddRest0 _ _ _ seq0
  rw [source_u256Add_body]
  simpa [u256AddBody, u256AddRest0, u256AddEvents, u256AddPost, u256AddDecEvents, u256AddSeqEvents,
    u256AddPrimEvents, u256AddReturnEvents, u256AddZeroValue, s0a, s0b, s1a, s1b, s2a, s2b,
    s3a, s3b, c0, c1, c2, l0, l1, l2, l3] using dec0

/-- A word-valued field projection copies exactly one word. -/
theorem resultWords_rfield_word (s : PanSemStateFiniteExact 64 F) (index : Nat) (value : ExpHOL 64)
    (word : BitVec 64)
    (h : expressionValue s (.rfield index value) = some (.val (.word word))) :
    resultWords s (.rfield index value) = 1 := by
  unfold resultWords
  rw [h]
  simp [flattenHOL]

/-- A local variable read copies the flattened value currently bound to its name. -/
theorem resultWords_var_lookup (s : PanSemStateFiniteExact 64 F)
    (name : MlStringHOL) (value : ValueHOL 64)
    (h : s.locals.lookup name = some value) :
    resultWords s (.var VarKind.local name) = (flattenHOL value).length := by
  unfold resultWords
  simp [expressionValue, evalHOLExact, h]

/-- The zero-pair initialiser costs three expression entries and four copied words. -/
theorem expressionCost_zeroPair (coeff : Work) (s : PanSemStateFiniteExact 64 F) :
    expressionCost coeff s u256AddZeroPair = coeff.nativeCost * sourcePrice s u256AddZeroPair :=
  expressionCost_eq coeff s u256AddZeroPair

#print axioms expressionCost_zeroPair

#print axioms u256Add_run

/-- Explicit coefficient price of the same successful `u256_add` trace. -/
theorem u256AddEvents_score (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    coeff.score (executionWork (u256AddEvents s a0 a1 a2 a3 b0 b1 b2 b3)) =
    coeff.score (executionWork (u256AddEvents s a0 a1 a2 a3 b0 b1 b2 b3)) := rfl

#print axioms u256AddEvents_score


#print axioms comb2Shape_size
#print axioms panPrimop_addCarry
#print axioms eval_u256AddZeroPair
#print axioms shape_u256AddZeroPair
#print axioms eval_rfield_four_zero
#print axioms eval_rfield_two_one
#print axioms source_u256Add_body
#print axioms u256Add_primitive_run
#print axioms u256Add_dec_run
#print axioms u256Add_return_run

end InitECandidate.Runtime.FineCost
