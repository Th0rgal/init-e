import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Prime
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Name permutation preserves the exact entry result at the same clock. -/
theorem pan_rename_entry_run {width : Nat} [NeZero width] {F : Type}
    (first second : MlS) (state : PanSemStateFiniteExact width F) (fuel : Nat)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width F)
    (run : evaluateHOLFiniteState {state with clock := fuel} (.call none first []) = (result,post)) :
    evaluateHOLFiniteState {{state with code := fpermCodeHOL first second state.code} with clock := fuel}
      (.call none second []) = (result,{post with code := fpermCodeHOL first second post.code}) := by
  have permutation := evaluateFpermPrimeHOL first second (.call none first []) state fuel
  rw [run] at permutation
  simpa [fpermHOL,fpermName] using permutation

#print axioms pan_rename_entry_run
end InitECandidate.Runtime
