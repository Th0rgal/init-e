import InitECandidate.Runtime.PanExpressionWork
import Flapjack.Pancake.PanToCrep
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Native word prices of Pan expressions. `exprPrices L G e` follows the
equations of `pan_to_crep$compile_exp` but returns, for each emitted Crep word,
its native Loop price `loopNodePrice`, together with the compiled shape. Local
variables are described by `L` (shape and word count) and global variables by
`G`; a global read is priced as its `pan_globals` expansion, a `TopAddr`-relative
structured load. Nothing here depends on slot names or address constants. -/

/-- Price of the words of a structured load from an address of price `p`:
the first word reads the address, each further word adds its offset. -/
def loadPrices (p : Nat) (offset : BitVec 64) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      (if offset == 0 then p + 21 else p + 98) ::
        loadPrices p (offset + BitVec.ofNat 64 (64 / 8)) count

/-- `comp_field` on prices: the slice of field `index`. -/
def fieldPrices (index : Nat) : List ShapeHOL → List Nat → List Nat × ShapeHOL
  | [], _ => ([19], .one)
  | shape :: shapes, prices =>
      if index = 0 then (prices.take (sizeOfShapeHOL shape), shape)
      else fieldPrices (index - 1) shapes (prices.drop (sizeOfShapeHOL shape))

/-- Price of the `TopAddr - c` address of a global. -/
def globalAddressPrice : Nat := 81 + 19 + 28 * 2 + 2

mutual
  /-- Word prices and shape of the Crep code `pan_to_crep` emits for `e`. -/
  def exprPrices (L G : MlStringHOL → Option (ShapeHOL × Nat)) :
      ExpHOL 64 → List Nat × ShapeHOL
    | .const _ => ([19], .one)
    | .var .local name =>
        match L name with
        | some (shape, count) => (List.replicate count 14, shape)
        | none => ([19], .one)
    | .var .global name =>
        match G name with
        | some (shape, count) => (loadPrices globalAddressPrice 0 count, shape)
        | none => ([19], .one)
    | .rstruct fields =>
        let compiled := exprListPrices L G fields
        (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
    | .rfield index record =>
        let compiled := exprPrices L G record
        match compiled.2 with
        | .comb shapes => fieldPrices index shapes compiled.1
        | _ => ([19], .one)
    | .nstruct _ _ => ([19], .one)
    | .nfield _ _ => ([19], .one)
    | .load shape address =>
        match exprPrices L G address with
        | (p :: _, _) => (loadPrices p 0 (sizeOfShapeHOL shape), shape)
        | ([], _) => ([19], .one)
    | .load32 address | .loadByte address =>
        match exprPrices L G address with
        | (p :: _, .one) => ([p + 49], .one)
        | _ => ([19], .one)
    | .op _ arguments =>
        match cexpHeads ((exprListPrices L G arguments).map Prod.fst) with
        | some heads => ([heads.sum + 28 * heads.length + 19 * (1 - heads.length) + 2], .one)
        | none => ([19], .one)
    | .panop _ arguments =>
        match cexpHeads ((exprListPrices L G arguments).map Prod.fst) with
        | some heads => ([heads.sum + 57], .one)
        | none => ([19], .one)
    | .cmp _ left right =>
        match exprPrices L G left, exprPrices L G right with
        | (a :: _, _), (b :: _, _) => ([a + b + 70], .one)
        | _, _ => ([19], .one)
    | .shift _ left right =>
        match exprPrices L G left, exprPrices L G right with
        | (a :: _, _), (b :: _, _) => ([a + b + 32], .one)
        | _, _ => ([19], .one)
    | .baseAddr => ([14], .one)
    | .topAddr => ([81], .one)
    | .bytesInWord => ([19], .one)
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def exprListPrices (L G : MlStringHOL → Option (ShapeHOL × Nat)) :
      List (ExpHOL 64) → List (List Nat × ShapeHOL)
    | [] => []
    | e :: es => exprPrices L G e :: exprListPrices L G es
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
  exprPrices (valueInfo s.locals) (valueInfo s.globals) e

/-- Native price of a source expression in a source state. -/
def sourcePrice {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) : Nat :=
  (sourcePrices s e).1.sum

#print axioms exprPrices
#print axioms sourcePrice
end InitECandidate.Runtime.FineCost
