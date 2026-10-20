import InitECandidate.Runtime.ActualPayloadHeaderPrefix
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.KeccakGlobalsFrame
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

end InitECandidate.Runtime
