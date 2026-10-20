import InitECandidate.Runtime.ActualPayloadHeaderWatched
import InitECandidate.Runtime.RunAttemptPayloadHeaderSource
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The callee binding built by the real `payload_header` call: its only parameter `si`
bound to the caller's `si` word. -/
def payloadHeaderCallee (si : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "si", .val (.word si))

/-- The actual entry state of the `payload_header` declaration call. -/
def payloadHeaderEntry {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  callEntryStateHOLFinite state (payloadHeaderCallee si)

theorem payloadHeaderEntry_clock {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).clock = state.clock - 1 := rfl

theorem payloadHeaderEntry_memory {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).memory = state.memory := rfl

theorem payloadHeaderEntry_memaddrs {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).memaddrs = state.memaddrs := rfl

theorem payloadHeaderEntry_globals {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).globals = state.globals := rfl

theorem payloadHeaderEntry_code {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).code = state.code := rfl

theorem payloadHeaderEntry_locals {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).locals = payloadHeaderCallee si := rfl

theorem payloadHeaderCallee_lookup (si : BitVec 64) :
    (payloadHeaderCallee si).lookup (ofString "si") = some (.val (.word si)) := by
  simp [payloadHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]

theorem payloadHeaderEntry_si {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64) :
    (payloadHeaderEntry state si).locals.lookup (ofString "si") = some (.val (.word si)) := by
  rw [payloadHeaderEntry_locals]
  exact payloadHeaderCallee_lookup si

/-- The single argument expression of the real call reads the caller's `si` word. -/
theorem payloadHeaderEntry_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si : BitVec 64) (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si))) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "si")] = some [.val (.word si)] := by
  simp only [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  rw [siLocal]

/-- The installed code resolves the real `payload_header` call to the actual source body and the
single-word callee binding. -/
theorem payloadHeaderEntry_lookup {F : Type} (state : PanSemStateFiniteExact 64 F) (si : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "payload_header") [.val (.word si)] =
      some (actualPayloadHeaderAt 0,payloadHeaderCallee si,.one) := by
  have installed : state.code.lookup (ofString "payload_header") =
      some ([(ofString "si",.one)],sourceFunctionBody Guest.guestFn_payload_header,.one) := by
    rw [code]; exact originalRuntimeCode_payloadHeader_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "payload_header") (ofString "si")
    (sourceFunctionBody Guest.guestFn_payload_header) si installed
  rw [lookup]
  have body : sourceFunctionBody Guest.guestFn_payload_header = actualPayloadHeaderAt 0 :=
    (sourceFunctionBody_eq_structural Guest.guestFn_payload_header).trans rfl
  rw [body]
  rfl

/-- **The actual `payload_header` call entry.**  Everything the watched 419-tick construction needs is
already true of the real declaration-call entry state: the parameter `si` is bound, memory, domains,
globals and code are the caller's, and the whole watched construction runs on that entry for 419
ticks, ending at statement 40 with the extra-length word installed at `h+136`.

The caller's clock must cover the call tick, hence `420`. -/
theorem actual_payload_header_call_entry {F : Type}
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
    (wordDomain : ∀ offset : Nat, offset < 248 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
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
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "si")] = some [.val (.word si)] ∧
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
    payloadHeaderEntry_arguments state si siLocal,
    payloadHeaderEntry_lookup state si code,?_⟩
  exact actual_payload_header_construction_0_to_40_watched (payloadHeaderEntry state si) si pl raw
    pointer extraLen st pad siEntry (by rw [domainEntry]; exact siDomain)
    (by rw [memEntry]; exact siCell) (by rw [domainEntry]; exact plDomain)
    (by rw [memEntry]; exact plCell) (codeEntry.trans code)
    (by rw [globalsEntry]; exact heapGlobal) aligned pointerBound
    (fun offset bound => by rw [domainEntry]; exact wordDomain offset bound)
    (fun offset bound => by rw [domainEntry]; exact byteDomain offset bound)
    (by rw [globalsEntry]; exact stateGlobal) (by rw [globalsEntry]; exact padGlobal)
    (fun address bound => by rw [domainEntry]; exact fullDomain address bound)
    below (by rw [memEntry]; exact plTwentyFourCell) outsideState outsidePad outsideOutput clockBudget

#print axioms payloadHeaderEntry_arguments
#print axioms payloadHeaderEntry_lookup
#print axioms actual_payload_header_call_entry

end InitECandidate.Runtime
