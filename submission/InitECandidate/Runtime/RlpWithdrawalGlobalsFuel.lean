import InitECandidate.Runtime.RlpWithdrawalHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A successful `encode_withdrawal_rlp` changes exactly one global, at *every* fuel: the clock
hypothesis of `rlpEncodeWithdrawal_returned_globals` is never used by its proof, and a callee that
returns normally at low fuel simply cannot happen. -/
theorem rlpEncodeWithdrawal_returned_globals_fuel {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals =
      (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd B 64))) t).globals := by
  rw [source_rlpEncodeWithdrawal_body,rlpEncodeWithdrawal_eq] at run
  obtain ⟨values,body,callee,returnShape,w,bodyPost,resumed,inner,argsR,lookupR,bodyRun,_,_,_,rcode,rglob,
    _,_,_,rrun,_,_,_,_,pg⟩ := decCall_returned_globalsG run
  have argsEval : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [(.const (64#64))] = some [.val (.word (64#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  rw [argsEval] at argsR
  cases argsR
  have installed : t.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  rw [pan_single_word_lookup t.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) (64#64) installed] at lookupR
  cases lookupR
  obtain ⟨_,_,hw,_,_,_,bcode,bg⟩ := alloc_body_returned _ bodyPost B 64 (by exact code) (by exact heap)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) w bodyRun
  subst hw
  have resumedCode : resumed.code = originalRuntimeCode := by
    rw [rcode,bcode]
    exact code
  have frame := wdDecP_globals_frame resumed resumedCode
  rw [rrun] at frame
  rw [pg]
  rw [frame,rglob]
  exact bg

/-- Fuel-free heap-pointer advance of a successful withdrawal encoder run. -/
theorem rlpEncodeWithdrawal_heap_fuel {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd B 64))) := by
  rw [rlpEncodeWithdrawal_returned_globals_fuel t base B value heap code run]
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Fuel-free global preservation of a successful withdrawal encoder run. -/
theorem rlpEncodeWithdrawal_other_globals_fuel {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64) (name : MlS)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode) (apart : name ≠ ofString "heap_ptr")
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals.lookup name = t.globals.lookup name := by
  rw [rlpEncodeWithdrawal_returned_globals_fuel t base B value heap code run]
  by_cases same : ofString "heap_ptr" = name
  · exact absurd same.symm apart
  · simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]

#print axioms rlpEncodeWithdrawal_returned_globals_fuel
#print axioms rlpEncodeWithdrawal_heap_fuel
#print axioms rlpEncodeWithdrawal_other_globals_fuel
end InitECandidate.Runtime
