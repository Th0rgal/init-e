import InitECandidate.Runtime.HtrWithdrawalBodyBound
import InitECandidate.Runtime.OriginalHtrWithdrawalCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrWithdrawal_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (w out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word w),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWithdrawalBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_withdrawal") arguments) (htrWithdrawalBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_withdrawal") =
      some ([(ofString "w",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_withdrawal,.one) := by
    rw [code]; exact originalRuntimeCode_htrWithdrawal_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_withdrawal") (ofString "w") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_withdrawal) w out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrWithdrawal_body _ w out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrWithdrawalBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrWithdrawal_call
end InitECandidate.Runtime
