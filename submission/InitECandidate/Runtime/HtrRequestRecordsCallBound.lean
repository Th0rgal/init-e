import InitECandidate.Runtime.HtrRequestRecordsBodyBound
import InitECandidate.Runtime.OriginalHtrRequestRecordsCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrDeposit_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (e out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word e),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrDepositBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_deposit") arguments) (htrDepositBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_deposit") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_deposit,.one) := by
    rw [code]; exact originalRuntimeCode_htrDeposit_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_deposit") (ofString "e") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_deposit) e out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrDeposit_body _ e out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrDepositBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrDeposit_call

theorem runBounded_htrWdreq_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (e out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word e),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWdreqBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_wdreq") arguments) (htrWdreqBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_wdreq") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_wdreq,.one) := by
    rw [code]; exact originalRuntimeCode_htrWdreq_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_wdreq") (ofString "e") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_wdreq) e out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrWdreq_body _ e out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrWdreqBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrWdreq_call

theorem runBounded_htrCons_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (e out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word e),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrConsBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_cons") arguments) (htrConsBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_cons") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_cons,.one) := by
    rw [code]; exact originalRuntimeCode_htrCons_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_cons") (ofString "e") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_cons) e out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrCons_body _ e out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrConsBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrCons_call

theorem runBounded_htrBdep_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (e out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word e),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBdepBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_bdep") arguments) (htrBdepBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_bdep") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_bdep,.one) := by
    rw [code]; exact originalRuntimeCode_htrBdep_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_bdep") (ofString "e") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_bdep) e out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrBdep_body _ e out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrBdepBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrBdep_call

theorem runBounded_htrBexit_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (e out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word e),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBexitBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_bexit") arguments) (htrBexitBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_bexit") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_bexit,.one) := by
    rw [code]; exact originalRuntimeCode_htrBexit_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htr_bexit") (ofString "e") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_bexit) e out (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrBexit_body _ e out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact cap
  · exact code
  · change htrBexitBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrBexit_call

end InitECandidate.Runtime
