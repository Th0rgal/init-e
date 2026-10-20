import InitECandidate.Runtime.PanTotalExpressionCost
import InitECandidate.Runtime.PanLoweringAllowance
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Local source units sufficient for scalar expression flattening. This is
not the final native coefficient vector. -/
def scalarLoweringWeights : Work := { expressions := 4, movedWords := 1 }

mutual
  def scalarLowering : ExpHOL 64 → Bool
    | .load .one address => scalarLowering address
    | .load _ _ => false
    | .rstruct fields | .op _ fields | .panop _ fields => scalarLoweringList fields
    | .rfield _ value | .load32 value | .loadByte value => scalarLowering value
    | .cmp _ left right | .shift _ left right => scalarLowering left && scalarLowering right
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def scalarLoweringList : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => scalarLowering head && scalarLoweringList tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

noncomputable def expressionListCost {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (es : List (ExpHOL 64)) : Nat := coeff.score (executionWork (expressionListEvents s es))

def LocalWidthsFit {F : Type} (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64) : Prop :=
  ∀ name shape names, context.vars.lookup name = some (shape, names) →
    names.length ≤ 1 + resultWords s (.var .local name)


end InitECandidate.Runtime.FineCost

#print axioms InitECandidate.Runtime.FineCost.expressionListCost
