import InitECandidate.Runtime.PanExpressionWork
import Flapjack.Pancake.PanToCrep
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Native word prices of Pan expressions, parameterized by a Crep node cost
`K`. `exprPrices K L G e` follows the equations of `pan_to_crep$compile_exp`
but returns, for each emitted Crep word, its price `nodePriceK K`, together with
the compiled shape. Local variables are described by `L` (shape and word count)
and global variables by `G`; a global read is priced as its `pan_globals`
expansion, a `TopAddr`-relative structured load. Nothing here depends on slot
names or address constants. The source charge uses `srcK`. -/

/-- Per-node Crep expression costs. `op n` is the surcharge of an `op` with `n`
arguments. -/
structure NodeK where
  cst : Nat
  var : Nat
  top : Nat
  load : Nat
  ld32 : Nat
  op : Nat → Nat
  crepOp : Nat
  shift : Nat
  cmp : Nat

mutual
  /-- Price of a Crep expression at node costs `K`. -/
  def nodePriceK (K : NodeK) : CrepExpHOL 64 → Nat
    | .const _ => K.cst
    | .var _ | .loadGlob _ | .baseAddr => K.var
    | .topAddr => K.top
    | .load address => nodePriceK K address + K.load
    | .load32 address | .loadByte address => nodePriceK K address + K.ld32
    | .op _ args => nodePriceListK K args + K.op args.length
    | .crepOp _ args => nodePriceListK K args + K.crepOp
    | .shift _ left right => nodePriceK K left + nodePriceK K right + K.shift
    | .cmp _ left right => nodePriceK K left + nodePriceK K right + K.cmp
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def nodePriceListK (K : NodeK) : List (CrepExpHOL 64) → Nat
    | [] => 0
    | head :: tail => nodePriceK K head + nodePriceListK K tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Default Loop leaf prices (`loopNodePrice`). -/
def loopK : NodeK where
  cst := 19
  var := 14
  top := 81
  load := 21
  ld32 := 49
  op := fun n => 28 * (n - 1) + 19 * (1 - (n - 1))
  crepOp := 57
  shift := 32
  cmp := 70

/-- Selector-derived prices (`selNodePrice`). -/
def selK : NodeK where
  cst := 24
  var := 24
  top := 124
  load := 24
  ld32 := 48
  op := fun n => 24 * (n - 1) + 24 * (1 - n)
  crepOp := 51
  shift := 28
  cmp := 85

/-- Source charge: the pointwise maximum of `loopK` and `selK`, so the source
pays both the default-Loop chain and the selector-priced chain. Provisional:
kept as a parameter for later spill/colour/native tightening. -/
def srcK : NodeK where
  cst := 24
  var := 24
  top := 124
  load := 24
  ld32 := 49
  op := fun n => max (28 * (n - 1) + 19 * (1 - (n - 1))) (24 * (n - 1) + 24 * (1 - n))
  crepOp := 57
  shift := 32
  cmp := 85

@[simp] theorem loopK_cst : loopK.cst = 19 := rfl
@[simp] theorem loopK_var : loopK.var = 14 := rfl
@[simp] theorem loopK_top : loopK.top = 81 := rfl
@[simp] theorem loopK_load : loopK.load = 21 := rfl
@[simp] theorem loopK_ld32 : loopK.ld32 = 49 := rfl
@[simp] theorem loopK_crepOp : loopK.crepOp = 57 := rfl
@[simp] theorem loopK_shift : loopK.shift = 32 := rfl
@[simp] theorem loopK_cmp : loopK.cmp = 70 := rfl
@[simp] theorem loopK_op (n : Nat) : loopK.op n = 28 * (n - 1) + 19 * (1 - (n - 1)) := rfl
@[simp] theorem selK_cst : selK.cst = 24 := rfl
@[simp] theorem selK_var : selK.var = 24 := rfl
@[simp] theorem selK_top : selK.top = 124 := rfl
@[simp] theorem selK_load : selK.load = 24 := rfl
@[simp] theorem selK_ld32 : selK.ld32 = 48 := rfl
@[simp] theorem selK_crepOp : selK.crepOp = 51 := rfl
@[simp] theorem selK_shift : selK.shift = 28 := rfl
@[simp] theorem selK_cmp : selK.cmp = 85 := rfl
@[simp] theorem selK_op (n : Nat) : selK.op n = 24 * (n - 1) + 24 * (1 - n) := rfl
@[simp] theorem srcK_cst : srcK.cst = 24 := rfl
@[simp] theorem srcK_var : srcK.var = 24 := rfl
@[simp] theorem srcK_top : srcK.top = 124 := rfl
@[simp] theorem srcK_load : srcK.load = 24 := rfl
@[simp] theorem srcK_ld32 : srcK.ld32 = 49 := rfl
@[simp] theorem srcK_crepOp : srcK.crepOp = 57 := rfl
@[simp] theorem srcK_shift : srcK.shift = 32 := rfl
@[simp] theorem srcK_cmp : srcK.cmp = 85 := rfl
@[simp] theorem srcK_op (n : Nat) : srcK.op n = max (28 * (n - 1) + 19 * (1 - (n - 1))) (24 * (n - 1) + 24 * (1 - n)) := rfl

/-- Price of the words of a structured load from an address of price `p`:
the first word reads the address, each further word adds its offset. -/
def loadPrices (K : NodeK) (p : Nat) (offset : BitVec 64) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      (if offset == 0 then p + K.load else p + K.cst + K.op 2 + K.load) ::
        loadPrices K p (offset + BitVec.ofNat 64 (64 / 8)) count

/-- `comp_field` on prices: the slice of field `index`. -/
def fieldPrices (K : NodeK) (index : Nat) : List ShapeHOL → List Nat → List Nat × ShapeHOL
  | [], _ => ([K.cst], .one)
  | shape :: shapes, prices =>
      if index = 0 then (prices.take (sizeOfShapeHOL shape), shape)
      else fieldPrices K (index - 1) shapes (prices.drop (sizeOfShapeHOL shape))

/-- Price of the `TopAddr - c` address of a global. -/
def globalAddressPrice (K : NodeK) : Nat := K.top + K.cst + K.op 2

mutual
  /-- Word prices and shape of the Crep code `pan_to_crep` emits for `e`. -/
  def exprPrices (K : NodeK) (L G : MlStringHOL → Option (ShapeHOL × Nat)) :
      ExpHOL 64 → List Nat × ShapeHOL
    | .const _ => ([K.cst], .one)
    | .var .local name =>
        match L name with
        | some (shape, count) => (List.replicate count K.var, shape)
        | none => ([K.cst], .one)
    | .var .global name =>
        match G name with
        | some (shape, count) => (loadPrices K (globalAddressPrice K) 0 count, shape)
        | none => ([K.cst], .one)
    | .rstruct fields =>
        let compiled := exprListPrices K L G fields
        (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
    | .rfield index record =>
        let compiled := exprPrices K L G record
        match compiled.2 with
        | .comb shapes => fieldPrices K index shapes compiled.1
        | _ => ([K.cst], .one)
    | .nstruct _ _ => ([K.cst], .one)
    | .nfield _ _ => ([K.cst], .one)
    | .load shape address =>
        match exprPrices K L G address with
        | (p :: _, _) => (loadPrices K p 0 (sizeOfShapeHOL shape), shape)
        | ([], _) => ([K.cst], .one)
    | .load32 address | .loadByte address =>
        match exprPrices K L G address with
        | (p :: _, .one) => ([p + K.ld32], .one)
        | _ => ([K.cst], .one)
    | .op _ arguments =>
        match cexpHeads ((exprListPrices K L G arguments).map Prod.fst) with
        | some heads => ([heads.sum + K.op heads.length], .one)
        | none => ([K.cst], .one)
    | .panop _ arguments =>
        match cexpHeads ((exprListPrices K L G arguments).map Prod.fst) with
        | some heads => ([heads.sum + K.crepOp], .one)
        | none => ([K.cst], .one)
    | .cmp _ left right =>
        match exprPrices K L G left, exprPrices K L G right with
        | (a :: _, _), (b :: _, _) => ([a + b + K.cmp], .one)
        | _, _ => ([K.cst], .one)
    | .shift _ left right =>
        match exprPrices K L G left, exprPrices K L G right with
        | (a :: _, _), (b :: _, _) => ([a + b + K.shift], .one)
        | _, _ => ([K.cst], .one)
    | .baseAddr => ([K.var], .one)
    | .topAddr => ([K.top], .one)
    | .bytesInWord => ([K.cst], .one)
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def exprListPrices (K : NodeK) (L G : MlStringHOL → Option (ShapeHOL × Nat)) :
      List (ExpHOL 64) → List (List Nat × ShapeHOL)
    | [] => []
    | e :: es => exprPrices K L G e :: exprListPrices K L G es
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! Source expression prices read the variable information from the source
state: each local or global keeps the shape and word count of its value. -/

/-- Shape and word count of the value of a source variable map entry. -/
def valueInfo {β : Type} (m : HolFiniteMapExact β (ValueHOL 64)) (name : β) :
    Option (ShapeHOL × Nat) :=
  (m.lookup name).map (fun value => (shapeOfHOLExact value, (flattenHOL value).length))

/-- Native word prices and shape of a source expression in a source state. -/
def sourcePrices {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    List Nat × ShapeHOL :=
  exprPrices srcK (valueInfo s.locals) (valueInfo s.globals) e

/-- Native price of a source expression in a source state. -/
def sourcePrice {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) : Nat :=
  (sourcePrices s e).1.sum

#print axioms exprPrices
#print axioms sourcePrice
end InitECandidate.Runtime.FineCost
