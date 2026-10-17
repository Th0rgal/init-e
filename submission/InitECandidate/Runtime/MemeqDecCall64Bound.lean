import InitECandidate.Runtime.MemeqBody64Bound
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual memeq declaration-call and a straight-line continuation have
total source-clock cost at most4n+1 for n≤64, including all early errors. -/
theorem evaluate_memeq_decCall64_straight_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : straightLine continuation = true)
    (leftArgument rightArgument sizeArgument : ExpHOL 64) (left right size : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [leftArgument,rightArgument,sizeArgument] = some [.val (.word left),.val (.word right),.val (.word size)])
    (small : size.toNat ≤ 64) (ticks : 4 * size.toNat + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "memeq") [leftArgument,rightArgument,sizeArgument] continuation);
    state.clock ≤ evaluated.2.clock + 4 * size.toNat + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "a",.val (.word left))).update (ofString "b",.val (.word right))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have localN : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,cost,remaining,noTimeout⟩ := evaluate_memeq_body64_bounded entry size localN small
    (by change 4 * size.toNat ≤ state.clock - 1; omega)
  have postCost : state.clock ≤ post.clock + 4 * size.toNat + 1 := by
    change state.clock - 1 ≤ post.clock + 4 * size.toNat at cost
    omega
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  have installed : state.code.lookup (ofString "memeq") =
      some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
    rw [code]
    exact originalRuntimeCode_memeq_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memeq) left right size (by decide) (by decide) (by decide) installed
  exact evaluate_decCall_straight_bounded state post name (ofString "memeq") .one .one
    [leftArgument,rightArgument,sizeArgument] [.val (.word left),.val (.word right),.val (.word size)]
    (sourceFunctionBody Guest.guestFn_memeq) continuation callee result (4 * size.toNat + 1)
    args lookup (by omega) body remaining postCost noTimeout supported

#print axioms evaluate_memeq_decCall64_straight_bounded
end InitECandidate.Runtime
