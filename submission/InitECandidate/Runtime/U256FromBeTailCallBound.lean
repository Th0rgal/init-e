import InitECandidate.Runtime.U256FromBeBodyBound
import InitECandidate.Runtime.OriginalU256FromBeCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanTailCallBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def u256FromBeCallee (pointer length : BitVec 64) :=
  (HolFiniteMapExact.empty.update (ofString "p",ValueHOL.val (.word pointer))).update
    (ofString "n",.val (.word length))

theorem evaluate_u256FromBe_tailCall_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64) (limit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (lengthBound : length.toNat ≤ limit)
    (four : 4 ≤ limit) (budget : limit + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call none (ofString "u256_from_be") arguments)
    state.clock ≤ evaluated.2.clock + (limit + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let callee := u256FromBeCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,u256FromBeCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,u256FromBeCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_u256FromBe_body_bounded entry pointer length limit atPointer atLength code lengthBound four
    (by change limit ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "u256_from_be") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_u256_from_be,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_u256FromBe_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "u256_from_be")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_u256_from_be)
    (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_u256_from_be) with
  | mk result post =>
    rw [run] at bound
    dsimp only at bound
    have clock : entry.clock = state.clock - 1 := rfl
    exact evaluate_tailCall_body_bounded state post (ofString "u256_from_be") arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_u256_from_be)
      callee (.comb [.one,.one,.one,.one]) result (limit + 1) args lookup (by omega) run
      (by omega) (by omega) bound.2.2.1

#print axioms evaluate_u256FromBe_tailCall_bounded
end InitECandidate.Runtime
