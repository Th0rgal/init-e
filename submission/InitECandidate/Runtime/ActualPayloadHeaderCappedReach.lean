import InitECandidate.Runtime.ActualPayloadHeaderWatched
import InitECandidate.Runtime.ActualPayloadHeaderCallReach
import InitECandidate.Runtime.ActualPayloadHeaderExtraLength
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- **The watched header construction with the header domain earned from the allocator guard.**

The public 419-tick composite takes the 248-byte header window as a domain premise.  That premise is
not an assumption: it follows from the modelled address space (`fullDomain`) as soon as the real
`alloc 248` guard holds (`pointer + 248 <= cap`); when the guard fails, the actual loader rejects the
request and the construction aborts, exactly as the source does.  This variant makes the trade
explicit: the success branch earns the window, the failure branch aborts. -/
theorem actual_payload_header_construction_0_to_40_watched_capped {F : Type}
    (state : PanSemStateFiniteExact 64 F) (si pl raw pointer extraLen st pad : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (below : pl.toNat + 136 ≤ pointer.toNat)
    (plTwentyFourCell : state.memory (pl + (24#64)) = .word extraLen)
    (outsideState : ¬ MWin st 200 (pl + (24#64)))
    (outsidePad : ¬ MWin pad 136 (pl + (24#64)))
    (outsideOutput : ¬ MWin (actualPayloadHeaderOhFloor pointer) 32 (pl + (24#64)))
    (budget : 419 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd (allocationEnd
            (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧
        post.memory (pointer + (136#64)) = .word extraLen) 419 (actualPayloadHeaderAt 40) := by
  by_cases room : pointer.toNat + 248 ≤ 33806089496
  · have wordDomain : ∀ offset : Nat, offset < 248 →
        state.memaddrs (pointer + BitVec.ofNat 64 offset) :=
      fun offset bound =>
        fullDomain _ (actual_payload_header_pointer_add_below pointer offset room bound)
    have byteDomain : ∀ offset : Nat, offset < 248 →
        state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) :=
      fun offset bound =>
        fullDomain _ (lt_of_le_of_lt (panByteAlignHOL_toNat_le (pointer + BitVec.ofNat 64 offset))
          (actual_payload_header_pointer_add_below pointer offset room bound))
    exact actual_payload_header_construction_0_to_40_watched state si pl raw pointer extraLen st pad
      siLocal siDomain siCell plDomain plCell code heapGlobal aligned pointerBound wordDomain byteDomain
      stateGlobal padGlobal fullDomain below plTwentyFourCell outsideState outsidePad outsideOutput budget
  · -- The real `alloc 248` guard fails: the loader rejects the request at statement 2.
    have first : Reaches state (actualPayloadHeaderAt 0)
        (fun next => next = setVarHOLFinite (ofString "pl") (.val (.word pl)) state) 0
        (actualPayloadHeaderAt 1) := by
      rw [source_actual_payload_header_pl]
      apply reaches_dec
      intro value evaluated
      rw [actual_payload_header_eval_load_word state (ofString "si") si (0#64) pl siLocal siDomain
        siCell] at evaluated
      cases Option.some.inj evaluated
      exact ⟨pl,rfl,rfl⟩
    have second : Reaches (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)
        (actualPayloadHeaderAt 1)
        (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw))
          (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) 0 (actualPayloadHeaderAt 2) := by
      rw [source_actual_payload_header_raw]
      apply reaches_dec
      intro found evaluated
      rw [actual_payload_header_eval_load_word (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)
        (ofString "pl") pl (0#64) raw
        (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
        (by simpa [setVarHOLFinite] using plDomain)
        (by simpa [setVarHOLFinite] using plCell)] at evaluated
      cases Option.some.inj evaluated
      exact ⟨raw,rfl,rfl⟩
    have loads : Reaches state (actualPayloadHeaderAt 0)
        (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw))
          (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) 0 (actualPayloadHeaderAt 2) :=
      reaches_trans state (actualPayloadHeaderAt 0) (actualPayloadHeaderAt 1) (actualPayloadHeaderAt 2)
        _ _ 0 0 first (fun E equal => equal ▸ second)
    have codeMid : (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).code = originalRuntimeCode := by
      simpa [setVarHOLFinite] using code
    have heapMid : (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).globals.lookup
        (ofString "heap_ptr") = some (.val (.word pointer)) := by
      simpa [setVarHOLFinite] using heapGlobal
    have clockMid : 2 ≤ (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)).clock := by
      simp [setVarHOLFinite]; omega
    have sizeNat : (248#64).toNat = 248 := by decide
    have over : 33806089496 < pointer.toNat + (248#64).toNat := by rw [sizeNat]; omega
    have rejected : Reaches (setVarHOLFinite (ofString "raw") (.val (.word raw))
        (setVarHOLFinite (ofString "pl") (.val (.word pl)) state)) (actualPayloadHeaderAt 2)
        (fun _ => False) 2 (actualPayloadHeaderAt 3) := by
      rw [source_actual_payload_header_alloc]
      exact actual_payload_header_alloc_rejected _ (ofString "h") (248#64) pointer
        (actualPayloadHeaderAt 3) (fun _ => False) heapMid codeMid clockMid pointerBound over
    have chain : Reaches state (actualPayloadHeaderAt 0) (fun _ => False) 2
        (actualPayloadHeaderAt 3) :=
      reaches_trans state (actualPayloadHeaderAt 0) (actualPayloadHeaderAt 2) (actualPayloadHeaderAt 3)
        _ _ 0 2 loads (fun E typed => typed ▸ rejected)
    rcases chain with ⟨E, impossible, _, _, _⟩ | ab
    · exact impossible.elim
    · exact Or.inr (stAbort_mono state _ 2 419 (by omega) ab)

/-- **The capped construction on the actual declaration-call entry.**  The header window is earned
from the modelled address space rather than assumed, so the call-site contract needs no room premise:
either the real guard holds and the watched construction runs, or the initial allocation aborts. -/
theorem actual_payload_header_call_entry_capped {F : Type}
    (state : PanSemStateFiniteExact 64 F) (si pl raw pointer extraLen st pad : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : state.memaddrs (si + (0#64)))
    (siCell : state.memory (si + (0#64)) = .word pl)
    (plDomain : state.memaddrs (pl + (0#64)))
    (plCell : state.memory (pl + (0#64)) = .word raw)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (below : pl.toNat + 136 ≤ pointer.toNat)
    (plTwentyFourCell : state.memory (pl + (24#64)) = .word extraLen)
    (outsideState : ¬ MWin st 200 (pl + (24#64)))
    (outsidePad : ¬ MWin pad 136 (pl + (24#64)))
    (outsideOutput : ¬ MWin (actualPayloadHeaderOhFloor pointer) 32 (pl + (24#64)))
    (budget : 420 ≤ state.clock) :
    (payloadHeaderEntry state si).clock = state.clock - 1 ∧
    (payloadHeaderEntry state si).memory = state.memory ∧
    (payloadHeaderEntry state si).memaddrs = state.memaddrs ∧
    (payloadHeaderEntry state si).globals = state.globals ∧
    (payloadHeaderEntry state si).code = originalRuntimeCode ∧
    (payloadHeaderEntry state si).locals.lookup (ofString "si") = some (.val (.word si)) ∧
    lookupCodeHOLFinite state.code.lookup (ofString "payload_header") [.val (.word si)] =
      some (actualPayloadHeaderAt 0,payloadHeaderCallee si,.one) ∧
    Reaches (payloadHeaderEntry state si) (actualPayloadHeaderAt 0)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer
          (allocationEnd (allocationEnd (allocationEnd (allocationEnd
            (actualPayloadHeaderTxrFloor pointer) (8#64)) (32#64)) (32#64)) (32#64)) ∧
        post.memory (pointer + (136#64)) = .word extraLen) 419 (actualPayloadHeaderAt 40) := by
  have siEntry : (payloadHeaderEntry state si).locals.lookup (ofString "si") =
      some (.val (.word si)) := payloadHeaderEntry_si state si
  have memEntry := payloadHeaderEntry_memory state si
  have domainEntry := payloadHeaderEntry_memaddrs state si
  have globalsEntry := payloadHeaderEntry_globals state si
  have codeEntry := payloadHeaderEntry_code state si
  have clockEntry := payloadHeaderEntry_clock state si
  have clockBudget : 419 ≤ (payloadHeaderEntry state si).clock := by omega
  refine ⟨clockEntry,memEntry,domainEntry,globalsEntry,codeEntry.trans code,siEntry,
    payloadHeaderEntry_lookup state si code,?_⟩
  exact actual_payload_header_construction_0_to_40_watched_capped (payloadHeaderEntry state si) si pl raw
    pointer extraLen st pad siEntry (by rw [domainEntry]; exact siDomain)
    (by rw [memEntry]; exact siCell) (by rw [domainEntry]; exact plDomain)
    (by rw [memEntry]; exact plCell) (codeEntry.trans code)
    (by rw [globalsEntry]; exact heapGlobal) aligned pointerBound
    (by rw [globalsEntry]; exact stateGlobal) (by rw [globalsEntry]; exact padGlobal)
    (fun address bound => by rw [domainEntry]; exact fullDomain address bound)
    below (by rw [memEntry]; exact plTwentyFourCell) outsideState outsidePad outsideOutput clockBudget

#print axioms actual_payload_header_construction_0_to_40_watched_capped
#print axioms actual_payload_header_call_entry_capped

end InitECandidate.Runtime
