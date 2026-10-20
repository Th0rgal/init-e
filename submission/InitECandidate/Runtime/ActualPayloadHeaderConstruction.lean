import InitECandidate.Runtime.ActualPayloadHeaderPrefix
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.AllocationFailureTail
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.DecodeRequestsBodyBound

namespace InitECandidate.Runtime

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual word and struct stores either abort or preserve construction bindings: the store changes
only memory, so the typed `h`, `pl`, `raw` locals, the `heap_ptr` global, the domain and the code all
survive.  This holds for the whole straight-line store ladder of `guestFn_payload_header`, including
the struct stores (`h[64] := rStruct [...]`, `h[160] := bf`), because neither operand is ever
evaluated: a failing address or value evaluation is an abort by itself. -/
theorem actual_payload_header_store_frame {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap) :
    Reaches mid (.seq (.store destination value) tail)
      (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 tail := by
  refine reaches_seq mid (.store destination value) tail 0 _ ?_
  rcases evaluate_store_cases mid destination value with error | ⟨memory,run⟩
  · refine Or.inr ?_
    unfold StAbort
    rw [error]
    exact ⟨.error,rfl,by simp,by simp,by simp,by simp⟩
  · exact Or.inl ⟨{mid with memory:=memory},facts,by simp,by simp,run⟩

#print axioms actual_payload_header_store_frame

/-- Statement 14 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_14 :
    ∃ destination value, actualPayloadHeaderAt 14 = .seq (.store destination value)
      (actualPayloadHeaderAt 15) := ⟨_,_,rfl⟩

/-- Statement 15 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_15 :
    ∃ destination value, actualPayloadHeaderAt 15 = .seq (.store destination value)
      (actualPayloadHeaderAt 16) := ⟨_,_,rfl⟩

/-- Statement 16 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_16 :
    ∃ destination value, actualPayloadHeaderAt 16 = .seq (.store destination value)
      (actualPayloadHeaderAt 17) := ⟨_,_,rfl⟩

/-- Statement 17 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_17 :
    ∃ destination value, actualPayloadHeaderAt 17 = .seq (.store destination value)
      (actualPayloadHeaderAt 18) := ⟨_,_,rfl⟩

/-- Statement 18 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_18 :
    ∃ destination value, actualPayloadHeaderAt 18 = .seq (.store destination value)
      (actualPayloadHeaderAt 19) := ⟨_,_,rfl⟩

/-- Statement 19 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_19 :
    ∃ destination value, actualPayloadHeaderAt 19 = .seq (.store destination value)
      (actualPayloadHeaderAt 20) := ⟨_,_,rfl⟩

/-- Statement 20 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_20 :
    ∃ destination value, actualPayloadHeaderAt 20 = .seq (.store destination value)
      (actualPayloadHeaderAt 21) := ⟨_,_,rfl⟩

/-- Statement 21 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_21 :
    ∃ destination value, actualPayloadHeaderAt 21 = .seq (.store destination value)
      (actualPayloadHeaderAt 22) := ⟨_,_,rfl⟩

/-- Statement 22 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_22 :
    ∃ destination value, actualPayloadHeaderAt 22 = .seq (.store destination value)
      (actualPayloadHeaderAt 23) := ⟨_,_,rfl⟩

/-- Statement 23 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_23 :
    ∃ destination value, actualPayloadHeaderAt 23 = .seq (.store destination value)
      (actualPayloadHeaderAt 24) := ⟨_,_,rfl⟩

/-- Statement 24 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_24 :
    ∃ destination value, actualPayloadHeaderAt 24 = .seq (.store destination value)
      (actualPayloadHeaderAt 25) := ⟨_,_,rfl⟩

/-- Statement 27 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_27 :
    ∃ destination value, actualPayloadHeaderAt 27 = .seq (.store destination value)
      (actualPayloadHeaderAt 28) := ⟨_,_,rfl⟩

/-- Statement 29 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_29 :
    ∃ destination value, actualPayloadHeaderAt 29 = .seq (.store destination value)
      (actualPayloadHeaderAt 30) := ⟨_,_,rfl⟩

/-- Statement 31 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_31 :
    ∃ destination value, actualPayloadHeaderAt 31 = .seq (.store destination value)
      (actualPayloadHeaderAt 32) := ⟨_,_,rfl⟩

/-- Statement 32 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_32 :
    ∃ destination value, actualPayloadHeaderAt 32 = .seq (.store destination value)
      (actualPayloadHeaderAt 33) := ⟨_,_,rfl⟩

/-- Statement 33 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_33 :
    ∃ destination value, actualPayloadHeaderAt 33 = .seq (.store destination value)
      (actualPayloadHeaderAt 34) := ⟨_,_,rfl⟩

/-- Statement 34 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_34 :
    ∃ destination value, actualPayloadHeaderAt 34 = .seq (.store destination value)
      (actualPayloadHeaderAt 35) := ⟨_,_,rfl⟩

/-- Statement 36 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_36 :
    ∃ destination value, actualPayloadHeaderAt 36 = .seq (.store destination value)
      (actualPayloadHeaderAt 37) := ⟨_,_,rfl⟩

/-- Statement 38 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_38 :
    ∃ destination value, actualPayloadHeaderAt 38 = .seq (.store destination value)
      (actualPayloadHeaderAt 39) := ⟨_,_,rfl⟩

/-- Statement 39 of the actual header construction is a single store. -/
theorem source_actual_payload_header_store_at_39 :
    ∃ destination value, actualPayloadHeaderAt 39 = .seq (.store destination value)
      (actualPayloadHeaderAt 40) := ⟨_,_,rfl⟩

/-- One actual store step of the header ladder, located by its statement index. -/
theorem actual_payload_header_store_step {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (index : Nat)
    (shape : ∃ destination value, actualPayloadHeaderAt index = .seq (.store destination value)
      (actualPayloadHeaderAt (index + 1)))
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap) :
    Reaches mid (actualPayloadHeaderAt index)
      (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 (actualPayloadHeaderAt (index + 1)) := by
  obtain ⟨destination, value, source⟩ := shape
  rw [source]
  exact actual_payload_header_store_frame state mid pl raw pointer heap destination value _ facts

#print axioms actual_payload_header_store_step

/-- Statement 25 is the actual `alloc 8` that produces `z8`. -/
theorem source_actual_payload_header_alloc_z8 :
    actualPayloadHeaderAt 25 = .decCall (ofString "z8") .one (ofString "alloc") [(.const (8#64))]
      (actualPayloadHeaderAt 26) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 26 is the actual `memzero(z8, 8)` call. -/
theorem source_actual_payload_header_memzero_z8 :
    actualPayloadHeaderAt 26 = .seq (.call (some (none,none)) (ofString "memzero")
      [.var .local (ofString "z8"), .const (8#64)]) (actualPayloadHeaderAt 27) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 28 is the actual struct declaration `bf := rStruct [...]` (value left opaque). -/
theorem source_actual_payload_header_dec_bf :
    ∃ shape initializer, actualPayloadHeaderAt 28 = .dec (ofString "bf") shape initializer
      (actualPayloadHeaderAt 29) := ⟨_,_,rfl⟩

/-- Statement 30 is the actual `alloc 32` that produces `wr`. -/
theorem source_actual_payload_header_alloc_wr :
    actualPayloadHeaderAt 30 = .decCall (ofString "wr") .one (ofString "alloc") [(.const (32#64))]
      (actualPayloadHeaderAt 31) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 35 is the actual `alloc 32` that produces `rh`. -/
theorem source_actual_payload_header_alloc_rh :
    actualPayloadHeaderAt 35 = .decCall (ofString "rh") .one (ofString "alloc") [(.const (32#64))]
      (actualPayloadHeaderAt 36) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 37 is the actual `alloc 32` that produces `bh`. -/
theorem source_actual_payload_header_alloc_bh :
    actualPayloadHeaderAt 37 = .decCall (ofString "bh") .one (ofString "alloc") [(.const (32#64))]
      (actualPayloadHeaderAt 38) := by
  unfold actualPayloadHeaderAt
  rfl

/-- An actual struct declaration of the header ladder: the initializer is never evaluated, so either
the shape or the evaluation of the initializer rejects (clock-free abort) or the binding is
introduced and the construction facts persist -- declarations touch only locals. -/
theorem actual_payload_header_dec_frame {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    (body : ProgHOL 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (namePl : name ≠ ofString "pl") (nameRaw : name ≠ ofString "raw") (nameH : name ≠ ofString "h") :
    Reaches mid (.dec name shape initializer body) (ActualPayloadHeaderPrefix state · pl raw pointer heap)
      0 body := by
  rw [Reaches, evaluateHOLFiniteState_dec_total]
  dsimp only
  cases he : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
    initializer with
  | none => exact Or.inr (stAbort_error mid 0)
  | some v =>
    by_cases ok : shapeEqHOL shape (shapeOfHOLExact v)
    · simp only [ok,if_true] at *
      obtain ⟨plLocal,rawLocal,hLocal,heapGlobal,domain,code⟩ := facts
      refine Or.inl ⟨setVarHOLFinite name v mid,?_,?_,?_,scoped_restore _ _⟩
      · refine ⟨?_,?_,?_,?_,?_,?_⟩
        · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namePl] using plLocal
        · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nameRaw] using rawLocal
        · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nameH] using hLocal
        · simpa only [setVarHOLFinite] using heapGlobal
        · simpa only [setVarHOLFinite] using domain
        · simpa only [setVarHOLFinite] using code
      · simp [setVarHOLFinite]
      · simp [setVarHOLFinite]
    · simp only [ok,if_false] at *
      refine Or.inr ⟨.error,rfl,by simp,by simp,by simp,by simp⟩

#print axioms actual_payload_header_dec_frame

/-- **Full-domain window readability.**  From the full `MEM_SIZE` domain of the runtime, every
allocation window of a header at `base` with `size` bytes is readable word by word and its byte
alignment addresses are in the domain too.  This derives the per-offset domain hypotheses of the
construction stages instead of assuming them. -/
theorem actual_payload_header_window_domain {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (size : Nat)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (fits : base.toNat + size ≤ 33806089496) :
    (∀ offset : Nat, offset < size → state.memaddrs (base + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < size →
        state.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 offset))) := by
  have addressToNat : ∀ offset : Nat, offset < size →
      (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    intro offset below
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_,?_⟩
  · intro offset below
    exact fullDomain _ (by rw [addressToNat offset below]; omega)
  · intro offset below
    exact fullDomain _ (by
      rw [panByteAlign_toNat64,addressToNat offset below]
      have := Nat.div_mul_le_self (base.toNat + offset) 8
      omega)

#print axioms actual_payload_header_window_domain

/-- The actual `memzero(z8, 8)` statement at index 26: it either rejects/errors or zeroes the eight
fresh bytes, and in every normal outcome the construction facts persist (only memory changes). -/
theorem actual_payload_header_memzero_z8_stage {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap z8 : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (z8Local : mid.locals.lookup (ofString "z8") = some (.val (.word z8)))
    (code : state.code = originalRuntimeCode)
    (small : z8.toNat + 8 ≤ 33806089496) (aligned : z8.toNat % 8 = 0)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 9 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 26) (ActualPayloadHeaderPrefix state · pl raw pointer heap)
      9 (actualPayloadHeaderAt 27) := by
  rw [source_actual_payload_header_memzero_z8]
  obtain ⟨window,bytes⟩ := actual_payload_header_window_domain state z8 8 fullDomain (by omega)
  have sizeNat : (8#64).toNat = 8 := by decide
  have arguments : evalListHOLFinite mid (h := fun address => Classical.propDecidable (mid.memaddrs address))
      [.var .local (ofString "z8"), .const (8#64)] =
      (some [ValueHOL.val (HolWordLab.word z8), ValueHOL.val (HolWordLab.word (8#64))] :
        Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,z8Local]
  obtain ⟨post, run, _, c1, c2, globals, postCode, domain, _, locals, _⟩ :=
    evaluate_memzero_aligned_call mid (.var .local (ofString "z8")) (.const (8#64)) z8 (8#64) arguments
      (by rw [facts.2.2.2.2.2]; exact code) (by omega) (by omega) aligned
      (fun offset below => by rw [facts.2.2.2.2.1]; exact window offset (by omega))
      (fun offset below => by rw [facts.2.2.2.2.1]; exact bytes offset (by omega))
  refine reaches_seq mid (.call (some (none,none)) (ofString "memzero")
    [.var .local (ofString "z8"), .const (8#64)]) (actualPayloadHeaderAt 27) 9 _ ?_
  refine Or.inl ⟨post,?_,by omega,by omega,run⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [locals] using facts.1
    · simpa [locals] using facts.2.1
    · simpa [locals] using facts.2.2.1
    · simpa [globals] using facts.2.2.2.1
    · simpa [domain] using facts.2.2.2.2.1
    · simpa [postCode] using facts.2.2.2.2.2

#print axioms actual_payload_header_memzero_z8_stage

/-- **The actual header construction from index 14 to the `block_rlp_length` call.**  Starting from
any state that carries the construction facts with heap pointer `heap` (in particular the normal
returned state of the actual `keccak256(tmp, 1, oh)` callee), the actual straight-line block of the
source -- the stores `h[16..144]`, the struct stores `h[64] := rStruct [...]` and `h[160] := bf`
through the opaque `bf` declaration, the four allocations `z8`, `wr`, `rh`, `bh`, the actual
`memzero(z8, 8)` and the remaining stores up to `h[240]` -- reaches index 40, immediately before the
actual `block_rlp_length(h, pl)` call, in 17 ticks, with every non-memory binding updated exactly as
the source says.  All failed loads, failed stores and allocation rejections are inside the abort
branch of the statement. -/
theorem actual_payload_header_construction_tail {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (small : heap.toNat + 8 ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 17 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 14)
      (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) 17 (actualPayloadHeaderAt 40) := by
  obtain ⟨bfShape, bfInitializer, decSpine⟩ := source_actual_payload_header_dec_bf
  have run1 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer heap) E →
      Reaches E (actualPayloadHeaderAt 14) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 (actualPayloadHeaderAt 25) := by
    intro E pE
    exact (reaches_trans E (actualPayloadHeaderAt 14) (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state E pl raw pointer heap 14 source_actual_payload_header_store_at_14 pE)
        (fun _E_2_ _pE_2_ => (reaches_trans _E_2_ (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _E_2_ pl raw pointer heap 15 source_actual_payload_header_store_at_15 _pE_2_)
        (fun __E_2__3_ __pE_2__3_ => (reaches_trans __E_2__3_ (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state __E_2__3_ pl raw pointer heap 16 source_actual_payload_header_store_at_16 __pE_2__3_)
        (fun ___E_2__3__4_ ___pE_2__3__4_ => (reaches_trans ___E_2__3__4_ (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ___E_2__3__4_ pl raw pointer heap 17 source_actual_payload_header_store_at_17 ___pE_2__3__4_)
        (fun ____E_2__3__4__5_ ____pE_2__3__4__5_ => (reaches_trans ____E_2__3__4__5_ (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ____E_2__3__4__5_ pl raw pointer heap 18 source_actual_payload_header_store_at_18 ____pE_2__3__4__5_)
        (fun _____E_2__3__4__5__6_ _____pE_2__3__4__5__6_ => (reaches_trans _____E_2__3__4__5__6_ (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _____E_2__3__4__5__6_ pl raw pointer heap 19 source_actual_payload_header_store_at_19 _____pE_2__3__4__5__6_)
        (fun ______E_2__3__4__5__6__7_ ______pE_2__3__4__5__6__7_ => (reaches_trans ______E_2__3__4__5__6__7_ (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ______E_2__3__4__5__6__7_ pl raw pointer heap 20 source_actual_payload_header_store_at_20 ______pE_2__3__4__5__6__7_)
        (fun _______E_2__3__4__5__6__7__8_ _______pE_2__3__4__5__6__7__8_ => (reaches_trans _______E_2__3__4__5__6__7__8_ (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _______E_2__3__4__5__6__7__8_ pl raw pointer heap 21 source_actual_payload_header_store_at_21 _______pE_2__3__4__5__6__7__8_)
        (fun ________E_2__3__4__5__6__7__8__9_ ________pE_2__3__4__5__6__7__8__9_ => (reaches_trans ________E_2__3__4__5__6__7__8__9_ (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 23) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ________E_2__3__4__5__6__7__8__9_ pl raw pointer heap 22 source_actual_payload_header_store_at_22 ________pE_2__3__4__5__6__7__8__9_)
        (fun _________E_2__3__4__5__6__7__8__9__10_ _________pE_2__3__4__5__6__7__8__9__10_ => (reaches_trans _________E_2__3__4__5__6__7__8__9__10_ (actualPayloadHeaderAt 23) (actualPayloadHeaderAt 24) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _________E_2__3__4__5__6__7__8__9__10_ pl raw pointer heap 23 source_actual_payload_header_store_at_23 _________pE_2__3__4__5__6__7__8__9__10_)
        (fun __________E_2__3__4__5__6__7__8__9__10__11_ __________pE_2__3__4__5__6__7__8__9__10__11_ => actual_payload_header_store_step state __________E_2__3__4__5__6__7__8__9__10__11_ pl raw pointer heap 24 source_actual_payload_header_store_at_24 __________pE_2__3__4__5__6__7__8__9__10__11_))))))))))))))))))))
  have run2 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) E →
      Reaches E (actualPayloadHeaderAt 27) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) 0 (actualPayloadHeaderAt 30) := by
    intro E pE
    refine reaches_trans E (actualPayloadHeaderAt 27) (actualPayloadHeaderAt 28) (actualPayloadHeaderAt 30)
      (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) 0 0
      (actual_payload_header_store_step state E pl raw pointer (allocationEnd heap (8#64)) 27 source_actual_payload_header_store_at_27 pE) ?_
    intro _E2 _pE2
    refine reaches_trans _E2 (actualPayloadHeaderAt 28) (actualPayloadHeaderAt 29) (actualPayloadHeaderAt 30)
      (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) 0 0 ?_ ?_
    · rw [decSpine]
      exact actual_payload_header_dec_frame state _E2 pl raw pointer (allocationEnd heap (8#64)) (ofString "bf") bfShape bfInitializer
        (actualPayloadHeaderAt 29) _pE2 (by decide) (by decide) (by decide)
    · intro _E3 _pE3
      exact actual_payload_header_store_step state _E3 pl raw pointer (allocationEnd heap (8#64)) 29 source_actual_payload_header_store_at_29 _pE3
  have run3 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) E →
      Reaches E (actualPayloadHeaderAt 31) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) 0 (actualPayloadHeaderAt 35) := by
    intro E pE
    exact (reaches_trans E (actualPayloadHeaderAt 31) (actualPayloadHeaderAt 32) (actualPayloadHeaderAt 35)
        (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) 0 0
        (actual_payload_header_store_step state E pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64)) 31 source_actual_payload_header_store_at_31 pE)
        (fun _E_2_ _pE_2_ => (reaches_trans _E_2_ (actualPayloadHeaderAt 32) (actualPayloadHeaderAt 33) (actualPayloadHeaderAt 35)
        (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) 0 0
        (actual_payload_header_store_step state _E_2_ pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64)) 32 source_actual_payload_header_store_at_32 _pE_2_)
        (fun __E_2__3_ __pE_2__3_ => (reaches_trans __E_2__3_ (actualPayloadHeaderAt 33) (actualPayloadHeaderAt 34) (actualPayloadHeaderAt 35)
        (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) 0 0
        (actual_payload_header_store_step state __E_2__3_ pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64)) 33 source_actual_payload_header_store_at_33 __pE_2__3_)
        (fun ___E_2__3__4_ ___pE_2__3__4_ => actual_payload_header_store_step state ___E_2__3__4_ pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64)) 34 source_actual_payload_header_store_at_34 ___pE_2__3__4_))))))
  have run4 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64))) E →
      Reaches E (actualPayloadHeaderAt 36) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64))) 0 (actualPayloadHeaderAt 37) := by
    intro E pE
    exact actual_payload_header_store_step state E pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) 36 source_actual_payload_header_store_at_36 pE
  have run5 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) E →
      Reaches E (actualPayloadHeaderAt 38) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) 0 (actualPayloadHeaderAt 40) := by
    intro E pE
    exact (reaches_trans E (actualPayloadHeaderAt 38) (actualPayloadHeaderAt 39) (actualPayloadHeaderAt 40)
        (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) 0 0
        (actual_payload_header_store_step state E pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64)) 38 source_actual_payload_header_store_at_38 pE)
        (fun _E_2_ _pE_2_ => actual_payload_header_store_step state _E_2_ pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64)) 39 source_actual_payload_header_store_at_39 _pE_2_))
  have allocZ8 : ∀ (E : PanSemStateFiniteExact 64 F), (ActualPayloadHeaderPrefix state · pl raw pointer heap) E → 2 ≤ E.clock →
      Reaches E (actualPayloadHeaderAt 25)
        (fun post => (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) post ∧
          post.locals.lookup (ofString "z8") = some (.val (.word heap))) 2 (actualPayloadHeaderAt 26) := by
    intro E pE clock
    exact (by
      rw [source_actual_payload_header_alloc_z8]
      exact actual_payload_header_alloc_next state E pl raw pointer heap (ofString "z8") (8#64)
        (actualPayloadHeaderAt 26) pE code (by decide) (by decide) (by decide) clock)
  have allocWr : ∀ (E : PanSemStateFiniteExact 64 F), (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) E → 2 ≤ E.clock →
      Reaches E (actualPayloadHeaderAt 30)
        (fun post => (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) post ∧
          post.locals.lookup (ofString "wr") = some (.val (.word (allocationEnd heap (8#64))))) 2 (actualPayloadHeaderAt 31) := by
    intro E pE clock
    exact (by
      rw [source_actual_payload_header_alloc_wr]
      exact actual_payload_header_alloc_next state E pl raw pointer (allocationEnd heap (8#64)) (ofString "wr") (32#64)
        (actualPayloadHeaderAt 31) pE code (by decide) (by decide) (by decide) clock)
  have allocRh : ∀ (E : PanSemStateFiniteExact 64 F), (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64))) E → 2 ≤ E.clock →
      Reaches E (actualPayloadHeaderAt 35)
        (fun post => (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64))) post ∧
          post.locals.lookup (ofString "rh") = some (.val (.word (allocationEnd (allocationEnd heap (8#64)) (32#64))))) 2 (actualPayloadHeaderAt 36) := by
    intro E pE clock
    exact (by
      rw [source_actual_payload_header_alloc_rh]
      exact actual_payload_header_alloc_next state E pl raw pointer (allocationEnd (allocationEnd heap (8#64)) (32#64)) (ofString "rh") (32#64)
        (actualPayloadHeaderAt 36) pE code (by decide) (by decide) (by decide) clock)
  have allocBh : ∀ (E : PanSemStateFiniteExact 64 F), (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64))) E → 2 ≤ E.clock →
      Reaches E (actualPayloadHeaderAt 37)
        (fun post => (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) post ∧
          post.locals.lookup (ofString "bh") = some (.val (.word (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64))))) 2 (actualPayloadHeaderAt 38) := by
    intro E pE clock
    exact (by
      rw [source_actual_payload_header_alloc_bh]
      exact actual_payload_header_alloc_next state E pl raw pointer (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (ofString "bh") (32#64)
        (actualPayloadHeaderAt 38) pE code (by decide) (by decide) (by decide) clock)
  have zeroZ8 : ∀ (E : PanSemStateFiniteExact 64 F), (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) E → E.locals.lookup (ofString "z8") = some (.val (.word heap)) →
      9 ≤ E.clock → Reaches E (actualPayloadHeaderAt 26) (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) 9 (actualPayloadHeaderAt 27) := by
    intro E pE z8Local clock
    exact actual_payload_header_memzero_z8_stage state E pl raw pointer (allocationEnd heap (8#64)) heap pE z8Local code small aligned fullDomain clock
  rcases run1 mid facts with ⟨E1, pE1, c1, c2, sc1⟩ | ab1
  · rcases allocZ8 E1 pE1 (by omega) with ⟨E2, pE2, d1, d2, sd⟩ | ab2
    · rcases zeroZ8 E2 pE2.1 pE2.2 (by omega) with ⟨E3, pE3, e1, e2, se⟩ | ab3
      · rcases run2 E3 pE3 with ⟨E4, pE4, f1, f2, sf⟩ | ab4
        · rcases allocWr E4 pE4 (by omega) with ⟨E5, pE5, g1, g2, sg⟩ | ab5
          · rcases run3 E5 pE5.1 with ⟨E6, pE6, h1, h2, sh⟩ | ab6
            · rcases allocRh E6 pE6 (by omega) with ⟨E7, pE7, i1, i2, si⟩ | ab7
              · rcases run4 E7 pE7.1 with ⟨E8, pE8, j1, j2, sj⟩ | ab8
                · rcases allocBh E8 pE8 (by omega) with ⟨E9, pE9, k1, k2, sk⟩ | ab9
                  · rcases run5 E9 pE9.1 with ⟨E10, pE10, l1, l2, sl⟩ | ab10
                    · refine Or.inl ⟨E10, pE10, by omega, by omega, ?_⟩
                      exact scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si) sj) sk) sl
                    · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab10
                      have ck := (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si) sj) sk).2.1
                      exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si) sj) sk).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
                  · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab9
                    have ck := (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si) sj).2.1
                    exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si) sj).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
                · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab8
                  have ck := (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si).2.1
                  exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh) si).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
              · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab7
                have ck := (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh).2.1
                exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg) sh).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
            · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab6
              have ck := (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg).2.1
              exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf) sg).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
          · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab5
            have ck := (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf).2.1
            exact Or.inr ⟨x, (scoped_trans (scoped_trans (scoped_trans (sc1) sd) se) sf).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
        · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab4
          have ck := (scoped_trans (scoped_trans (sc1) sd) se).2.1
          exact Or.inr ⟨x, (scoped_trans (scoped_trans (sc1) sd) se).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
      · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab3
        have ck := (scoped_trans (sc1) sd).2.1
        exact Or.inr ⟨x, (scoped_trans (sc1) sd).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
    · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab2
      have ck := (sc1).2.1
      exact Or.inr ⟨x, (sc1).1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
  · exact Or.inr (stAbort_mono mid _ 0 17 (by omega) ab1)

#print axioms actual_payload_header_construction_tail

/-- Statement 23 is the actual store `h[136] := load [pl + 24]` that carries the payload extra
length into the header. -/
theorem source_actual_payload_header_store_136 :
    actualPayloadHeaderAt 23 = .seq (.store (.op .add [.var .local (ofString "h"), .const (136#64)])
      (.load .one (.op .add [.var .local (ofString "pl"), .const (24#64)]))) (actualPayloadHeaderAt 24) := by
  unfold actualPayloadHeaderAt
  rfl

/-- **The `h[136]` extra-length cell.**  The actual store `h[136] := load [pl + 24]` reads the extra
length word from the payload and writes it into the header cell at `pointer + 136`; a failed load or a
missing header cell is again a clock-free abort. -/
theorem actual_payload_header_store_136_stage {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap extraLen : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (plDomain : mid.memaddrs (pl + (24#64)))
    (plCell : mid.memory (pl + (24#64)) = .word extraLen)
    (headerDomain : mid.memaddrs (pointer + (136#64))) :
    Reaches mid (actualPayloadHeaderAt 23)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer heap ∧
        post.memory (pointer + (136#64)) = .word extraLen) 0 (actualPayloadHeaderAt 24) := by
  rw [source_actual_payload_header_store_136]
  have destination : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a))
      (.op .add [.var .local (ofString "h"), .const (136#64)]) =
      (some (ValueHOL.val (HolWordLab.word (pointer + (136#64)))) : Option (ValueHOL 64)) :=
    actual_payload_header_eval_word_add mid (ofString "h") pointer (136#64) facts.2.2.1
  have value : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "pl"), .const (24#64)])) =
      (some (ValueHOL.val (HolWordLab.word extraLen)) : Option (ValueHOL 64)) :=
    actual_payload_header_eval_load mid (ofString "pl") pl (24#64) extraLen facts.1 plDomain plCell
  have run := actual_payload_header_store_any mid _ _ (pointer + (136#64)) extraLen destination value
    headerDomain
  refine reaches_seq mid (.store (.op .add [.var .local (ofString "h"), .const (136#64)])
    (.load .one (.op .add [.var .local (ofString "pl"), .const (24#64)]))) (actualPayloadHeaderAt 24) 0 _ ?_
  refine Or.inl ⟨sourceWriteWord mid (pointer + (136#64)) extraLen,⟨ActualPayloadHeaderPrefix.write facts,?_⟩,
    by simp [sourceWriteWord],by simp [sourceWriteWord],run⟩
  simp [sourceWriteWord]

#print axioms actual_payload_header_store_136_stage

/-- **The actual `keccak256` call shape used by the header construction.** -/
def actualPayloadHeaderKeccak : ProgHOL 64 :=
  .call (some (none,none)) (ofString "keccak256")
    [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")]

/-- Statement 9 is the actual `keccak256(tmp, 1, oh)` call. -/
theorem source_actual_payload_header_keccak_shape :
    actualPayloadHeaderAt 9 = .seq actualPayloadHeaderKeccak (actualPayloadHeaderAt 10) := by
  unfold actualPayloadHeaderAt actualPayloadHeaderKeccak
  rfl

/-- The actual `keccak256(tmp, 1, oh)` call preserves every global of the runtime, in every
outcome -- including the allocator global `heap_ptr`. -/
theorem actual_payload_header_keccak_globals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.globals = state.globals := by
  have frame := keccak_call_globals_frame (F := F)
    [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] state code
  simpa only [actualPayloadHeaderKeccak] using frame

#print axioms actual_payload_header_keccak_globals

/-- Consequently the allocator binding survives the actual keccak call. -/
theorem actual_payload_header_keccak_heap_ptr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.globals.lookup (ofString "heap_ptr") =
      state.globals.lookup (ofString "heap_ptr") := by
  rw [actual_payload_header_keccak_globals state code]

#print axioms actual_payload_header_keccak_heap_ptr

/-- On a normal return the actual `keccak256(tmp, 1, oh)` call gives back the callee's final state
with the caller's locals restored verbatim; in particular `h`, `pl`, `raw`, `oh` and `tmp` keep their
words after the call. -/
theorem actual_payload_header_keccak_normal_locals {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state actualPayloadHeaderKeccak = (none, mid)) :
    ∃ postState : PanSemStateFiniteExact 64 F, mid = {postState with locals := state.locals} := by
  classical
  simp only [actualPayloadHeaderKeccak,evaluateHOLFiniteState_call] at run
  split at run
  · exact absurd run (by simp)
  · split at run
    · exact absurd run (by simp)
    · split at run
      · exact absurd run (by simp)
      · repeat' first | split at run | skip
        all_goals (try (exact absurd run (by simp)))
        all_goals (try (repeat' first | split at run | skip))
        all_goals (first
          | exact ⟨_,by simpa using congrArg Prod.snd run.symm⟩
          | exact absurd run (by simp))

#print axioms actual_payload_header_keccak_normal_locals

/-- **The complete post-keccak construction facts.**  Everything the construction needs about the
state returned by the actual `keccak256(tmp, 1, oh)` call survives the call: the caller's locals are
restored verbatim, the globals (hence `heap_ptr`) are untouched, and the general evaluation metadata
theorem gives `mid.code = before.code` and `mid.memaddrs = before.memaddrs` for every program and
every outcome.  This is the transport that lets the construction continue after the real call. -/
theorem actual_payload_header_commit_after_keccak {F : Type} (state before mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp : BitVec 64)
    (pre : ActualPayloadHeaderCommit state before pl raw pointer heap oh tmp)
    (code : before.code = originalRuntimeCode)
    (normal : evaluateHOLFiniteState before actualPayloadHeaderKeccak = (none, mid)) :
    ActualPayloadHeaderCommit state mid pl raw pointer heap oh tmp := by
  obtain ⟨postState, equal⟩ := actual_payload_header_keccak_normal_locals before mid normal
  subst equal
  have globals := actual_payload_header_keccak_globals before code
  rw [normal] at globals
  have picture := evaluateHOLFiniteState_metadata before actualPayloadHeaderKeccak
  rw [normal] at picture
  obtain ⟨plLocal,rawLocal,hLocal,heapGlobal,domain,codeFrame⟩ := pre.1
  obtain ⟨ohLocal,tmpLocal⟩ := pre.2
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · simpa using plLocal
  · simpa using rawLocal
  · simpa using hLocal
  · have globalEq : postState.globals = before.globals := by simpa using globals
    rw [globalEq]
    exact heapGlobal
  · rw [picture.2.1]; exact domain
  · rw [picture.1]; exact codeFrame
  · simpa using ohLocal
  · simpa using tmpLocal

#print axioms actual_payload_header_commit_after_keccak

/-- **The actual header construction from the keccak return to `block_rlp_length`.**  From the state
returned by the actual `keccak256(tmp, 1, oh)` call, the rest of the source -- the stores
`h[16..240]` with the struct stores and the opaque `bf` declaration, the allocations `txr`, `z8`,
`wr`, `rh`, `bh`, the actual `memzero(z8, 8)` and the extra-length cell `h[136]` -- reaches index 40,
immediately before the actual `block_rlp_length(h, pl)` call, in 19 ticks. -/
theorem actual_payload_header_construction_from_keccak {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp : BitVec 64)
    (facts : ActualPayloadHeaderCommit state mid pl raw pointer heap oh tmp)
    (code : state.code = originalRuntimeCode)
    (wordDomain : ∀ offset : Nat, offset < 256 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (small : (allocationEnd heap (32#64)).toNat + 8 ≤ 33806089496)
    (aligned : (allocationEnd heap (32#64)).toNat % 8 = 0)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 19 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 10)
      (ActualPayloadHeaderPrefix state · pl raw pointer
        (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (32#64)) (8#64))
          (32#64)) (32#64)) (32#64))) 19 (actualPayloadHeaderAt 40) := by
  have after := actual_payload_header_construction_after_keccak state mid pl raw pointer heap oh tmp facts
    code wordDomain (by omega)
  rcases after with ⟨E1, pE1, c1, c2, sc1⟩ | ab
  · have tail := actual_payload_header_construction_tail state E1 pl raw pointer
      (allocationEnd heap (32#64)) pE1.1.1 code small aligned fullDomain (by omega)
    rcases tail with ⟨E2, pE2, d1, d2, sd⟩ | ab2
    · refine Or.inl ⟨E2, pE2, by omega, by omega, scoped_trans sc1 sd⟩
    · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab2
      have ck := sc1.2.1
      exact Or.inr ⟨x, sc1.1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
  · exact Or.inr (stAbort_mono mid _ 2 19 (by omega) ab)

#print axioms actual_payload_header_construction_from_keccak

/-- **The actual allocator callee never returns normally once the request overflows.**  When the
unsigned request guard `cap - heap_ptr < size` fires, the original allocator runs its trap and skips
the rounding, the heap assignment and the successful return, so it cannot return a value. -/
theorem actual_payload_header_alloc_body_no_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (size heap : BitVec 64)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : s.code = originalRuntimeCode)
    (below : heap.toNat ≤ 33806089496) (over : 33806089496 < heap.toNat + size.toNat)
    (output : ValueHOL 64) :
    (evaluateHOLFiniteState (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))))
      (sourceFunctionBody Guest.guestFn_alloc)).1 ≠ some (.returned output) := by
  have enteredP : (setVarHOLFinite (ofString "p") (.val (.word heap))
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))))).locals.lookup
      (ofString "p") = (some (ValueHOL.val (HolWordLab.word heap)) : Option (ValueHOL 64)) := by
    change ((HolFiniteMapExact.empty.update (ofString "n",ValueHOL.val (HolWordLab.word size))).update
      (ofString "p",ValueHOL.val (HolWordLab.word heap))).lookup (ofString "p") = _
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredN : (setVarHOLFinite (ofString "p") (.val (.word heap))
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))))).locals.lookup
      (ofString "n") = (some (ValueHOL.val (HolWordLab.word size)) : Option (ValueHOL 64)) := by
    change ((HolFiniteMapExact.empty.update (ofString "n",ValueHOL.val (HolWordLab.word size))).update
      (ofString "p",ValueHOL.val (HolWordLab.word heap))).lookup (ofString "n") = _
    simp [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "p" ≠ ofString "n" from by decide]
  have enteredCode : (setVarHOLFinite (ofString "p") (.val (.word heap))
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))))).code =
      originalRuntimeCode := by
    show s.code = originalRuntimeCode
    exact code
  have heapEval : @evalHOLExact 64 F _
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))).toExact
      (fun a => Classical.propDecidable ((callEntryStateHOLFinite s
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))).memaddrs a))
      (.var .global (ofString "heap_ptr")) =
      (some (ValueHOL.val (HolWordLab.word heap)) : Option (ValueHOL 64)) := by
    simp [evalHOLExact,callEntryStateHOLFinite,heapGlobal]
  have capNat : (33806089496 : BitVec 64).toNat = 33806089496 := by decide
  have request : ((33806089496 : BitVec 64) - heap).toNat < size.toNat := by
    have sub := BitVec.toNat_sub_of_le (x := (33806089496 : BitVec 64)) (y := heap) (by
      show heap.toNat ≤ (33806089496 : BitVec 64).toNat
      rw [capNat]
      exact below)
    rw [sub, capNat]
    omega
  have failed := evaluate_allocationAfterPointer_failure
    (setVarHOLFinite (ofString "p") (.val (.word heap))
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))))
    heap size enteredCode enteredP enteredN request
  obtain ⟨failureRun,_,_⟩ := failed
  have resultRun : (evaluateHOLFiniteState (callEntryStateHOLFinite s
        (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))))
      (sourceFunctionBody Guest.guestFn_alloc)).1 =
      (evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word heap))
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))))
        (.call (some (none,none)) (ofString "trap_with") [.const 1])).1 := by
    rw [source_alloc_body,evaluateHOLFiniteState_dec_total]
    simp only [heapEval]
    simp only [shapeOfHOLExact,shapeEqHOL,if_true]
    rw [failureRun]
  intro returned
  rw [resultRun] at returned
  exact evaluate_discard_call_no_return _ (ofString "trap_with") [.const 1] output returned

#print axioms actual_payload_header_alloc_body_no_return

/-- **The actual `alloc` rejects an excessive request.**  When the request does not fit the memory,
the real allocator traps, so the allocation statement terminates in the abort branch of the reach
relation -- no successful allocation is assumed. -/
theorem actual_payload_header_alloc_rejected {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (size heap : BitVec 64) (continuation : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : s.code = originalRuntimeCode) (budget : 2 ≤ s.clock)
    (below : heap.toNat ≤ 33806089496) (over : 33806089496 < heap.toNat + size.toNat) :
    Reaches s (.decCall name .one (ofString "alloc") [(.const size)] continuation) P 2 continuation := by
  have arguments : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [(.const size)] = (some [ValueHOL.val (HolWordLab.word size)] : Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  refine bounded_decCall_reaches s name (ofString "alloc") .one .one [(.const size)]
    [ValueHOL.val (HolWordLab.word size)] (sourceFunctionBody Guest.guestFn_alloc) continuation
    (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))) 1 P arguments ?_ budget ?_ ?_
  · rw [pan_single_word_lookup _ (ofString "alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_alloc)
      size (by rw [code]; exact originalRuntimeCode_allocation_lookup)]
  · have bound := evaluate_source_alloc_uniform_bounded
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))) code
      (by change 1 ≤ s.clock - 1; omega)
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  · intro value post returned shapes
    exact absurd (congrArg Prod.fst returned)
      (actual_payload_header_alloc_body_no_return s size heap heapGlobal code below over value)

#print axioms actual_payload_header_alloc_rejected

/-- **The guarded actual `alloc` step.**  This is the wrapper that removes the room assumption: the
allocation either succeeds (the normal branch, carrying the construction facts and the new heap
floor) or the real allocator rejects the request and the statement ends in its abort branch.  Nothing
about successful room is assumed; only that the current floor itself is inside the memory. -/
theorem actual_payload_header_alloc_guarded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (size heap : BitVec 64) (continuation : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : s.code = originalRuntimeCode) (budget : 2 ≤ s.clock)
    (below : heap.toNat ≤ 33806089496)
    (property : ∀ post : PanSemStateFiniteExact 64 F,
      post.memory = s.memory → post.memaddrs = s.memaddrs → post.code = s.code →
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap size))) s).globals →
      P (setVarHOLFinite name (.val (.word heap)) {post with locals := s.locals})) :
    Reaches s (.decCall name .one (ofString "alloc") [(.const size)] continuation) P 2 continuation := by
  by_cases room : heap.toNat + size.toNat ≤ 33806089496
  · exact actual_payload_header_alloc_step s name size heap continuation P heapGlobal code budget property
  · exact actual_payload_header_alloc_rejected s name size heap continuation P heapGlobal code budget below
      (by omega)

#print axioms actual_payload_header_alloc_guarded

/-- **The `z8` allocation with the room question settled by the real allocator.**  No reserve is
assumed: either the request fits and the allocation succeeds with the new heap floor, or the real
allocator rejects it and the statement ends in the abort branch.  The success branch records the room
it earned, which is exactly the guard the following `memzero(z8, 8)` needs. -/
theorem actual_payload_header_alloc_z8_room {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (below : heap.toNat ≤ 33806089496)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 25)
      (fun post => ActualPayloadHeaderPrefix state post pl raw pointer (allocationEnd heap (8#64)) ∧
        post.locals.lookup (ofString "z8") = some (.val (.word heap)) ∧
        heap.toNat + (8#64).toNat ≤ 33806089496) 2 (actualPayloadHeaderAt 26) := by
  rw [source_actual_payload_header_alloc_z8]
  by_cases room : heap.toNat + (8#64).toNat ≤ 33806089496
  · have property : ∀ post : PanSemStateFiniteExact 64 F,
        post.memory = mid.memory → post.memaddrs = mid.memaddrs → post.code = mid.code →
        post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap (8#64)))) mid).globals →
        (ActualPayloadHeaderPrefix state (setVarHOLFinite (ofString "z8") (.val (.word heap))
            {post with locals := mid.locals}) pl raw pointer (allocationEnd heap (8#64)) ∧
          (setVarHOLFinite (ofString "z8") (.val (.word heap)) {post with locals := mid.locals}).locals.lookup
            (ofString "z8") = some (.val (.word heap)) ∧
          heap.toNat + (8#64).toNat ≤ 33806089496) := by
      intro post memory domain postCode globals
      refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,room⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "z8" ≠ ofString "pl" from by decide,facts.1]
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "z8" ≠ ofString "raw" from by decide,facts.2.1]
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "z8" ≠ ofString "h" from by decide,facts.2.2.1]
      · simp only [setVarHOLFinite]
        rw [globals]
        simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simp only [setVarHOLFinite]
        rw [domain]
        exact facts.2.2.2.2.1
      · simp only [setVarHOLFinite]
        rw [postCode]
        exact facts.2.2.2.2.2
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    exact actual_payload_header_alloc_step mid (ofString "z8") (8#64) heap (actualPayloadHeaderAt 26) _
      facts.2.2.2.1 (by rw [facts.2.2.2.2.2]; exact code) budget property
  · exact actual_payload_header_alloc_rejected mid (ofString "z8") (8#64) heap (actualPayloadHeaderAt 26)
      _ facts.2.2.2.1 (by rw [facts.2.2.2.2.2]; exact code) budget below (by omega)

#print axioms actual_payload_header_alloc_z8_room

/-- **The `z8` window and its actual `memzero`.**  From a state holding the construction facts at
index 25 with `heap + 8` inside the memory and an eight-byte aligned floor, the actual `alloc 8` and
the actual `memzero(z8, 8)` clear eight bytes at the returned floor and hand on the bumped heap, in
11 ticks -- or the allocation is rejected and the statement aborts.  No reserve is assumed. -/
theorem actual_payload_header_z8_guarded {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (below : heap.toNat ≤ 33806089496) (alignedHeap : heap.toNat % 8 = 0)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 11 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 25)
      (ActualPayloadHeaderPrefix state · pl raw pointer (allocationEnd heap (8#64))) 11
      (actualPayloadHeaderAt 27) := by
  have first := actual_payload_header_alloc_z8_room state mid pl raw pointer heap facts code below (by omega)
  rcases first with ⟨E1, pE1, c1, c2, sc1⟩ | ab
  · have second := actual_payload_header_memzero_z8_stage state E1 pl raw pointer
      (allocationEnd heap (8#64)) heap pE1.1 pE1.2.1 code pE1.2.2 alignedHeap fullDomain (by omega)
    rcases second with ⟨E2, pE2, d1, d2, sd⟩ | ab2
    · refine Or.inl ⟨E2, pE2, by omega, by omega, scoped_trans sc1 sd⟩
    · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab2
      have ck := sc1.2.1
      exact Or.inr ⟨x, sc1.1.trans a1, a2, by omega, by omega, fun t => a5 (by omega)⟩
  · exact Or.inr (stAbort_mono mid _ 2 11 (by omega) ab)

#print axioms actual_payload_header_z8_guarded

/-- **A later allocation floor never moves backwards.**  When the rounded request does not overflow,
the allocator floor after an allocation is at least the floor before it. -/
theorem actual_payload_header_floor_lower (pointer size : BitVec 64)
    (fits : pointer.toNat + size.toNat + 7 < 2^64) :
    pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat := by
  have seven : (7#64 : BitVec 64).toNat = 7 := by decide
  have inner : (pointer + size).toNat = pointer.toNat + size.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  have sum : (pointer + size + (7#64)).toNat = pointer.toNat + size.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by rw [inner,seven]; omega),inner,seven]
  rw [allocationEnd_eq_align,panByteAlign_toNat64]
  change pointer.toNat + size.toNat ≤ BitVec.toNat (pointer + size + (7#64)) / 8 * 8
  rw [sum]
  have split := Nat.div_add_mod (pointer.toNat + size.toNat + 7) 8
  have small := Nat.mod_lt (pointer.toNat + size.toNat + 7) (by norm_num : 0 < 8)
  omega

#print axioms actual_payload_header_floor_lower

/-- **The `z8` floor lies past the whole header.**  With the header's own allocation and the two
allocations that follow it, the floor the `z8` allocation starts from is at or above
`heap_ptr + 248`, hence strictly past the extra-length cell at `heap_ptr + 136`. -/
theorem actual_payload_header_z8_lower (heap : BitVec 64)
    (below : heap.toNat ≤ 33806089496) :
    heap.toNat + 248 ≤ (allocationEnd (allocationEnd (allocationEnd heap (248#64)) (32#64)) (32#64)).toNat := by
  have one : (248#64 : BitVec 64).toNat = 248 := by decide
  have two : (32#64 : BitVec 64).toNat = 32 := by decide
  have upper : ∀ (p n : BitVec 64), p.toNat + n.toNat + 7 < 2^64 →
      (allocationEnd p n).toNat ≤ p.toNat + n.toNat + 7 := by
    intro p n bound
    have seven : (7#64 : BitVec 64).toNat = 7 := by decide
    have inner : (p + n).toNat = p.toNat + n.toNat := by
      rw [BitVec.toNat_add_of_lt (by omega)]
    have sum : (p + n + (7#64)).toNat = p.toNat + n.toNat + 7 := by
      rw [BitVec.toNat_add_of_lt (by rw [inner,seven]; omega),inner,seven]
    rw [allocationEnd_eq_align,panByteAlign_toNat64]
    change BitVec.toNat (p + n + (7#64)) / 8 * 8 ≤ p.toNat + n.toNat + 7
    rw [sum]
    have := Nat.div_mul_le_self (p.toNat + n.toNat + 7) 8
    omega
  have first := actual_payload_header_floor_lower heap (248#64) (by rw [one]; omega)
  have firstUp := upper heap (248#64) (by rw [one]; omega)
  have second := actual_payload_header_floor_lower (allocationEnd heap (248#64)) (32#64)
    (by rw [two]; omega)
  have secondUp := upper (allocationEnd heap (248#64)) (32#64) (by rw [two]; omega)
  have third := actual_payload_header_floor_lower
    (allocationEnd (allocationEnd heap (248#64)) (32#64)) (32#64) (by rw [two]; omega)
  omega

#print axioms actual_payload_header_z8_lower

/-- **The extra-length cell is outside the `z8` window.**  The cell `heap_ptr + 136` written by
statement 23 is strictly below the `z8` floor, so the actual `memzero(z8, 8)` cannot touch it. -/
theorem actual_payload_header_extra_cell_not_z8 (heap z8 : BitVec 64)
    (floor : z8 = allocationEnd (allocationEnd (allocationEnd heap (248#64)) (32#64)) (32#64))
    (below : heap.toNat ≤ 33806089496) :
    heap + (136#64) ≠ z8 := by
  have lower := actual_payload_header_z8_lower heap below
  have cell : (heap + (136#64)).toNat = heap.toNat + 136 := by
    have h : (136#64 : BitVec 64).toNat = 136 := by decide
    rw [BitVec.toNat_add_of_lt (by rw [h]; omega),h]
  intro same
  rw [floor] at same
  have values := congrArg BitVec.toNat same
  rw [cell] at values
  omega

#print axioms actual_payload_header_extra_cell_not_z8

/-- **The whole header lies below the later allocation floors.**  Every address inside the 248-byte
header block allocated by statement 2 is strictly below the floor the `z8` allocation starts from, so
none of the later allocations, stores or the actual `memzero(z8, 8)` can touch a header cell such as
the extra-length cell at `heap_ptr + 136`.  This is the geometry the `block_rlp_length` runtime
argument uses. -/
theorem actual_payload_header_header_below_floors (heap : BitVec 64)
    (below : heap.toNat ≤ 33806089496) :
    ∀ headerAddress : BitVec 64, heap.toNat ≤ headerAddress.toNat → headerAddress.toNat < heap.toNat + 248 →
      headerAddress.toNat < (allocationEnd (allocationEnd (allocationEnd heap (248#64)) (32#64)) (32#64)).toNat := by
  intro headerAddress headerAbove headerBelow
  have lower := actual_payload_header_z8_lower heap below
  omega

#print axioms actual_payload_header_header_below_floors

/-- **A store to a different address keeps a cell.**  The actual word store only replaces the cell it
writes, so any cell with a different address keeps its value. -/
theorem actual_payload_header_write_keeps_cell {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (written value cell : BitVec 64) (distinct : cell ≠ written) :
    (sourceWriteWord state written value).memory cell = state.memory cell := by
  simp [sourceWriteWord,distinct]

#print axioms actual_payload_header_write_keeps_cell

/-- **Distinct header cells stay distinct.**  Two different constant offsets inside the header block
address different cells, so the later header stores never overwrite the extra-length cell at offset
136. -/
theorem actual_payload_header_offset_distinct (pointer : BitVec 64) (first second : Nat)
    (room : pointer.toNat + 256 < 2^64) (distinct : first ≠ second)
    (firstBound : first < 256) (secondBound : second < 256) :
    pointer + BitVec.ofNat 64 first ≠ pointer + BitVec.ofNat 64 second := by
  have firstNat : (BitVec.ofNat 64 first).toNat = first := by
    rw [BitVec.toNat_ofNat]
    omega
  have secondNat : (BitVec.ofNat 64 second).toNat = second := by
    rw [BitVec.toNat_ofNat]
    omega
  intro same
  have values := congrArg BitVec.toNat same
  rw [BitVec.toNat_add_of_lt (by rw [firstNat]; omega),
    BitVec.toNat_add_of_lt (by rw [secondNat]; omega),firstNat,secondNat] at values
  exact distinct (by omega)

#print axioms actual_payload_header_offset_distinct

/-- **The actual keccak call as a reach step.**  Statement 9 is the actual `keccak256(tmp, 1, oh)`
call.  Whatever the callee does, the statement either continues at statement 10 with the concrete
construction facts restored -- the caller's locals verbatim, globals and `heap_ptr` untouched, code
and memory addresses preserved by the general metadata theorem -- or it ends in the abort branch
within its 360-tick budget. -/
theorem actual_payload_header_keccak_reaches {F : Type} (ref state : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp st pad : BitVec 64)
    (facts : ActualPayloadHeaderCommit ref state pl raw pointer heap oh tmp)
    (code : state.code = originalRuntimeCode)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (ticks : 360 ≤ state.clock)
    (stateSmall : st.toNat + 200 ≤ 33806089496) (stateAligned : st.toNat % 8 = 0)
    (stateWords : ∀ offset : Nat, offset < 200 → state.memaddrs (st + BitVec.ofNat 64 offset))
    (stateBytes : ∀ offset : Nat, offset < 200 →
      state.memaddrs (panByteAlignHOL (st + BitVec.ofNat 64 offset)))
    (small : pad.toNat + 136 ≤ 33806089496) (padAligned : pad.toNat % 8 = 0)
    (tmpAligned : tmp.toNat % 8 = 0) (ohAligned : oh.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 →
      state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < 1 → state.memaddrs (tmp + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < 1 →
      state.memaddrs (panByteAlignHOL (tmp + BitVec.ofNat 64 offset))) :
    Reaches state (actualPayloadHeaderAt 9)
      (ActualPayloadHeaderCommit ref · pl raw pointer heap oh tmp) 360 (actualPayloadHeaderAt 10) := by
  have bounded := actual_payload_header_keccak_call_bounded state tmp oh st pad facts.2.2 facts.2.1
    stateGlobal padGlobal code ticks stateSmall stateAligned stateWords stateBytes small padAligned
    tmpAligned ohAligned words bytes sourceWords sourceBytes
  rw [source_actual_payload_header_keccak_shape]
  refine reaches_seq state actualPayloadHeaderKeccak (actualPayloadHeaderAt 10) 360 _ ?_
  unfold RunBounded at bounded
  change state.clock ≤ (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock + 360 ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 ≠ some .timeOut at bounded
  by_cases normal : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = none
  · obtain ⟨post,run⟩ : ∃ post : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState state actualPayloadHeaderKeccak = (none, post) :=
      ⟨_, by rw [Prod.eq_iff_fst_eq_snd_eq]; exact ⟨normal,rfl⟩⟩
    refine Or.inl ⟨post,?_,?_,?_,run⟩
    · exact actual_payload_header_commit_after_keccak ref state post pl raw pointer heap oh tmp
        facts code run
    · have spent := bounded.1
      rw [run] at spent
      exact spent
    · have kept := bounded.2.1
      rw [run] at kept
      exact kept
  · obtain ⟨x,run⟩ : ∃ result, (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = some result := by
      cases placed : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 with
      | none => exact absurd placed normal
      | some result => exact ⟨result,rfl⟩
    refine Or.inr ⟨x,run,?_,bounded.1,bounded.2.1,?_⟩
    · intro value returned
      have discard := evaluate_discard_call_no_return state (ofString "keccak256")
        [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] value
      exact discard (run.trans (congrArg some returned))
    · intro clock budget
      have different := bounded.2.2
      rw [run] at different
      exact different (congrArg some budget)


#print axioms actual_payload_header_keccak_reaches

/-- **The header stores from statement 14 to statement 25.**  Every store in the range is free and
only changes memory, the opaque `bf` declaration is free and only rebinds locals, so the construction
reaches the actual `alloc 8` for `z8` in zero ticks, or aborts there. -/
theorem actual_payload_header_stores_to_z8 {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap) :
    Reaches mid (actualPayloadHeaderAt 14) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0
      (actualPayloadHeaderAt 25) := by
  have run1 : ∀ E : PanSemStateFiniteExact 64 F, (ActualPayloadHeaderPrefix state · pl raw pointer heap) E →
      Reaches E (actualPayloadHeaderAt 14) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0
        (actualPayloadHeaderAt 25) := by
    intro E pE
    exact (reaches_trans E (actualPayloadHeaderAt 14) (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state E pl raw pointer heap 14 source_actual_payload_header_store_at_14 pE)
        (fun _E_2_ _pE_2_ => (reaches_trans _E_2_ (actualPayloadHeaderAt 15) (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _E_2_ pl raw pointer heap 15 source_actual_payload_header_store_at_15 _pE_2_)
        (fun __E_2__3_ __pE_2__3_ => (reaches_trans __E_2__3_ (actualPayloadHeaderAt 16) (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state __E_2__3_ pl raw pointer heap 16 source_actual_payload_header_store_at_16 __pE_2__3_)
        (fun ___E_2__3__4_ ___pE_2__3__4_ => (reaches_trans ___E_2__3__4_ (actualPayloadHeaderAt 17) (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ___E_2__3__4_ pl raw pointer heap 17 source_actual_payload_header_store_at_17 ___pE_2__3__4_)
        (fun ____E_2__3__4__5_ ____pE_2__3__4__5_ => (reaches_trans ____E_2__3__4__5_ (actualPayloadHeaderAt 18) (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ____E_2__3__4__5_ pl raw pointer heap 18 source_actual_payload_header_store_at_18 ____pE_2__3__4__5_)
        (fun _____E_2__3__4__5__6_ _____pE_2__3__4__5__6_ => (reaches_trans _____E_2__3__4__5__6_ (actualPayloadHeaderAt 19) (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _____E_2__3__4__5__6_ pl raw pointer heap 19 source_actual_payload_header_store_at_19 _____pE_2__3__4__5__6_)
        (fun ______E_2__3__4__5__6__7_ ______pE_2__3__4__5__6__7_ => (reaches_trans ______E_2__3__4__5__6__7_ (actualPayloadHeaderAt 20) (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ______E_2__3__4__5__6__7_ pl raw pointer heap 20 source_actual_payload_header_store_at_20 ______pE_2__3__4__5__6__7_)
        (fun _______E_2__3__4__5__6__7__8_ _______pE_2__3__4__5__6__7__8_ => (reaches_trans _______E_2__3__4__5__6__7__8_ (actualPayloadHeaderAt 21) (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _______E_2__3__4__5__6__7__8_ pl raw pointer heap 21 source_actual_payload_header_store_at_21 _______pE_2__3__4__5__6__7__8_)
        (fun ________E_2__3__4__5__6__7__8__9_ ________pE_2__3__4__5__6__7__8__9_ => (reaches_trans ________E_2__3__4__5__6__7__8__9_ (actualPayloadHeaderAt 22) (actualPayloadHeaderAt 23) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state ________E_2__3__4__5__6__7__8__9_ pl raw pointer heap 22 source_actual_payload_header_store_at_22 ________pE_2__3__4__5__6__7__8__9_)
        (fun _________E_2__3__4__5__6__7__8__9__10_ _________pE_2__3__4__5__6__7__8__9__10_ => (reaches_trans _________E_2__3__4__5__6__7__8__9__10_ (actualPayloadHeaderAt 23) (actualPayloadHeaderAt 24) (actualPayloadHeaderAt 25)
        (ActualPayloadHeaderPrefix state · pl raw pointer heap) (ActualPayloadHeaderPrefix state · pl raw pointer heap) 0 0
        (actual_payload_header_store_step state _________E_2__3__4__5__6__7__8__9__10_ pl raw pointer heap 23 source_actual_payload_header_store_at_23 _________pE_2__3__4__5__6__7__8__9__10_)
        (fun __________E_2__3__4__5__6__7__8__9__10__11_ __________pE_2__3__4__5__6__7__8__9__10__11_ => actual_payload_header_store_step state __________E_2__3__4__5__6__7__8__9__10__11_ pl raw pointer heap 24 source_actual_payload_header_store_at_24 __________pE_2__3__4__5__6__7__8__9__10__11_))))))))))))))))))))
  exact run1 mid facts

#print axioms actual_payload_header_stores_to_z8

/-- **The construction tail under a rejected `z8` allocation.**  When the `alloc 8` request does not
fit, the real allocator rejects it, so the stores of statements 14 to 24 lead straight into the abort
branch within the two ticks the allocation itself needs. -/
theorem actual_payload_header_tail_rejected {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (below : heap.toNat ≤ 33806089496)
    (noRoom : 33806089496 < heap.toNat + (8#64).toNat)
    (budget : 2 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 14)
      (ActualPayloadHeaderPrefix state · pl raw pointer
        (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) 2
      (actualPayloadHeaderAt 40) := by
  rcases actual_payload_header_stores_to_z8 state mid pl raw pointer heap facts with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · have rejected := actual_payload_header_alloc_rejected E (ofString "z8") (8#64) heap
      (actualPayloadHeaderAt 26) (fun _ => False) pE.2.2.2.1
      (by rw [pE.2.2.2.2.2]; exact code) (by omega) below noRoom
    rcases rejected with ⟨bad, impossible, _, _, _⟩ | ab2
    · exact (by simpa using impossible : False).elim
    · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab2
      have bridge : (evaluateHOLFiniteState E (ProgHOL.decCall (ofString "z8") ShapeHOL.one
            (ofString "alloc") [ExpHOL.const (8#64)] (actualPayloadHeaderAt 26))).2.clock =
          (evaluateHOLFiniteState E (actualPayloadHeaderAt 25)).2.clock := rfl
      have sameClock : E.clock = mid.clock := by omega
      have clocks := sc.2.1
      refine Or.inr ⟨x, sc.1.trans a1, a2, by omega, by omega, ?_⟩
      intro t
      exact a5 (by omega)
  · obtain ⟨x, a1, a2, a3, a4, a5⟩ := ab
    exact Or.inr ⟨x, a1, a2, by omega, a4, fun t => a5 (by omega)⟩

#print axioms actual_payload_header_tail_rejected

/-- **The construction tail for every outcome, without any room reserve.**  From statement 14 the
actual construction reaches statement 40 -- immediately before `block_rlp_length(h, pl)` -- in 17
ticks, or aborts: the room the `memzero(z8, 8)` needs is either granted by the real allocator or the
allocator rejects the request and the statement ends in the abort branch.  Only the current floor's own
membership in memory and its eight-byte alignment are assumed. -/
theorem actual_payload_header_tail_guarded {F : Type} (state mid : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap : BitVec 64)
    (facts : ActualPayloadHeaderPrefix state mid pl raw pointer heap)
    (code : state.code = originalRuntimeCode)
    (below : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (fullDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 17 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 14)
      (ActualPayloadHeaderPrefix state · pl raw pointer
        (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64))) 17
      (actualPayloadHeaderAt 40) := by
  by_cases room : heap.toNat + (8#64).toNat ≤ 33806089496
  · exact actual_payload_header_construction_tail state mid pl raw pointer heap facts code room aligned
      fullDomain budget
  · exact reaches_mono mid (actualPayloadHeaderAt 14) (actualPayloadHeaderAt 40)
      (ActualPayloadHeaderPrefix state · pl raw pointer
        (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64)))
      (ActualPayloadHeaderPrefix state · pl raw pointer
        (allocationEnd (allocationEnd (allocationEnd (allocationEnd heap (8#64)) (32#64)) (32#64)) (32#64)))
      2 17 (by omega) (fun _ h => h)
      (actual_payload_header_tail_rejected state mid pl raw pointer heap facts code below (by omega) (by omega))

#print axioms actual_payload_header_tail_guarded

/-- **An allocation floor never exceeds its request by more than seven bytes.** -/
theorem actual_payload_header_floor_upper (pointer size : BitVec 64)
    (fits : pointer.toNat + size.toNat + 7 < 2^64) :
    (allocationEnd pointer size).toNat ≤ pointer.toNat + size.toNat + 7 := by
  have seven : (7#64 : BitVec 64).toNat = 7 := by decide
  have inner : (pointer + size).toNat = pointer.toNat + size.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  have sum : (pointer + size + (7#64)).toNat = pointer.toNat + size.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by rw [inner,seven]; omega),inner,seven]
  rw [allocationEnd_eq_align,panByteAlign_toNat64]
  change BitVec.toNat (pointer + size + (7#64)) / 8 * 8 ≤ pointer.toNat + size.toNat + 7
  rw [sum]
  have := Nat.div_mul_le_self (pointer.toNat + size.toNat + 7) 8
  omega

#print axioms actual_payload_header_floor_upper

/-- **Allocation floors are eight-byte aligned.** -/
theorem actual_payload_header_floor_aligned (pointer size : BitVec 64) :
    (allocationEnd pointer size).toNat % 8 = 0 := by
  rw [allocationEnd_eq_align,panByteAlign_toNat64]
  have split := Nat.div_add_mod (pointer + size + (7#64)).toNat 8
  have small := Nat.mod_lt (pointer + size + (7#64)).toNat (by norm_num : 0 < 8)
  omega

#print axioms actual_payload_header_floor_aligned

end InitECandidate.Runtime
