import InitECandidate.Runtime.AddSatReturnedExactContext
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Quantitative composition for the exact original add_sat declaration.
The continuation is its concrete computed call-entry state, not an assumed
callee runtime or semantic relation. -/
theorem runBounded_add_sat_declaration {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (left right : BitVec 64) (tailCost : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word left),.val (.word right)])
 (code : s.code=originalRuntimeCode) (budget : 1+tailCost≤s.clock)
 (inner : RunBounded (setVarHOLFinite name (.val (.word (wordAddSat left right))) {s with clock:=s.clock-1}) tail tailCost) :
 RunBounded s (.decCall name .one (ofString "add_sat") arguments tail) (1+tailCost) := by
 have installed : s.code.lookup (ofString "add_sat")=some addSatCodeEntry := by rw [code];exact vmLookup_add_sat
 unfold RunBounded at inner ⊢
 rw [evaluate_addSat_decCall s name arguments tail left right installed args (by omega)]
 dsimp only at inner ⊢
 change s.clock-1≤_+tailCost ∧_≤s.clock-1 ∧_ at inner
 exact ⟨by have:=inner.1;omega,by have:=inner.2.1;omega,inner.2.2⟩
#print axioms runBounded_add_sat_declaration
end InitECandidate.Runtime
