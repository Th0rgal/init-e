import InitECandidate.Runtime.StatelessMidSource
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclaration
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem reaches_loadDec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (name : MlS) (a : ExpHOL 64) (A : BitVec 64)
    (body : ProgHOL 64)
    (ha : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) a = some (.val (.word A))) :
    Reaches t (.dec name .one (.load .one a) body)
      (fun E => t.memaddrs A ∧ E = setVarHOLFinite name (.val (.word (memWord t.memory A))) t) 0 body := by
  apply reaches_dec
  intro v hv
  by_cases dom : t.memaddrs A
  · have load : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (.load .one a) =
        some (.val (.word (memWord t.memory A))) := by
      rw [evalHOLExact]; simp [ha, memLoadHOLExact, isWfShapeExactHOL, dom, memWord]
    rw [load] at hv
    exact ⟨_, (Option.some.inj hv).symm, dom, rfl⟩
  · have load : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (.load .one a) = none := by
      rw [evalHOLExact]; simp [ha, memLoadHOLExact, isWfShapeExactHOL, dom]
    rw [load] at hv; cases hv

theorem eval_op_word {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs] (op : BinOp)
    (args : List (ExpHOL 64)) (v : ValueHOL 64) (h : evalHOLExact st (.op op args) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rw [evalHOLExact] at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, _, rfl⟩ := h
      exact ⟨w, rfl⟩
    · cases h
  · cases h

theorem reaches_storeWord {σ : Type} (t : PanSemStateFiniteExact 64 σ) (dest e : ExpHOL 64) (A : BitVec 64)
    (cont : ProgHOL 64)
    (hd : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) dest = some (.val (.word A)))
    (hword : ∀ v, @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    Reaches t (.seq (.store dest e) cont)
      (fun E => ∃ x, @evalHOLExact 64 σ _ t.toExact (fun y => Classical.propDecidable (t.memaddrs y)) e =
        some (.val (.word x)) ∧ t.memaddrs A ∧ E = ({t with memory := wmem t.memory A x} : PanSemStateFiniteExact 64 σ))
      0 cont := by
  apply reaches_seq
  cases hv : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e with
  | none =>
    right; rw [evaluateHOLFiniteState_store, hd]; simp only [hv]; exact stAbort_error t 0
  | some v =>
    obtain ⟨x, rfl⟩ := hword _ hv
    by_cases dom : t.memaddrs A
    · exact Or.inl ⟨_, ⟨x, rfl, dom, rfl⟩, by simp, by simp, sszStore_in t A x dest e hd hv dom⟩
    · right; rw [sszStore_out t A x dest e hd hv dom]; exact stAbort_error t 0

theorem reaches_guard {σ : Type} (t : PanSemStateFiniteExact 64 σ) (cond : ExpHOL 64) (c : BitVec 64)
    (cont : ProgHOL 64) (code : t.code = originalRuntimeCode) :
    Reaches t (.seq (.ite cond (stFail c) .skip) cont)
      (fun E => E = t ∧ @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond =
        some (.val (.word 0))) 1 cont := by
  apply reaches_seq
  rcases stGuard_cases t cond c code with ⟨c0, r0⟩ | ab
  · exact Or.inl ⟨t, ⟨rfl, c0⟩, by omega, le_refl _, r0⟩
  · exact Or.inr ab

/-- The actual allocation declaration of 96 bytes. -/
theorem reaches_alloc96 {σ : Type} (t : PanSemStateFiniteExact 64 σ) (name : MlS) (cont : ProgHOL 64) (H : BitVec 64)
    (code : t.code = originalRuntimeCode)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (pointerBound : H.toNat ≤ 33806089496) :
    Reaches t (.decCall name .one (ofString "alloc") [.const 96] cont)
      (fun E => (96 : BitVec 64) ≤ (33806089496 : BitVec 64) - H ∧ ∃ ready : PanSemStateFiniteExact 64 σ,
        ready.clock = t.clock - 1 ∧ ready.memory = t.memory ∧ ready.locals = t.locals ∧ ready.code = t.code ∧
        ready.memaddrs = t.memaddrs ∧
        ready.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd H 96))) t).globals ∧
        E = setVarHOLFinite name (.val (.word H)) ready) 2 cont := by
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      [.const 96] = some [.val (.word 96)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  by_cases request : (96 : BitVec 64) ≤ (33806089496 : BitVec 64) - H
  · by_cases zero : t.clock = 0
    · right
      rw [evaluateHOLFiniteState_decCall_total, args]
      simp only [zero, if_true]
      split <;> exact ⟨_, rfl, by simp, by simp [emptyLocalsHOLFinite], by simp [emptyLocalsHOLFinite], fun h => by omega⟩
    · obtain ⟨ready, _, rclock, rmem, rlocals, rcode, rdom, _, _, rglobals, decl⟩ :=
        evaluate_alloc_call_and_declaration t _ H 96 args code zero heap request
          (allocationEnd_within_heap H _ pointerBound request)
      left
      refine ⟨setVarHOLFinite name (.val (.word H)) ready,
        ⟨request, ready, rclock, rmem, rlocals, rcode, rdom, rglobals, rfl⟩, ?_, ?_, ?_⟩
      · show t.clock ≤ ready.clock + 2; omega
      · show ready.clock ≤ t.clock; omega
      · rw [decl name cont]; exact scoped_restore _ _
  · have over : ((33806089496 : BitVec 64) - H).toNat < (96 : BitVec 64).toNat := by
      rw [BitVec.le_def] at request; omega
    have f1 := evaluate_alloc_request_failure_declaration t _ H 96 name .one cont args code heap over
    right
    cases run : evaluateHOLFiniteState t (.decCall name .one (ofString "alloc") [.const 96] cont) with
    | mk r post =>
      rw [run] at f1
      obtain ⟨n1, c1⟩ := f1
      cases r with
      | none => exact absurd rfl n1
      | some x =>
        refine ⟨x, rfl, fun v h => ?_, ?_, ?_, fun en => ?_⟩
        · have nr := evaluate_alloc_request_failure_declaration_no_return t _ H 96 name .one cont v args code heap over
          rw [run] at nr; exact nr (by rw [h])
        · show t.clock ≤ post.clock + 2; dsimp only at c1; omega
        · show post.clock ≤ t.clock; dsimp only at c1; omega
        · have nt := evaluate_alloc_request_failure_declaration_no_timeout t _ H 96 name .one cont args code heap over en
          rw [run] at nt; exact fun h => nt (by rw [h])

/-- The actual three-offset check call. -/
theorem reaches_midCheck {σ : Type} (t : PanSemStateFiniteExact 64 σ) (cont : ProgHOL 64) (offsets NL : BitVec 64)
    (code : t.code = originalRuntimeCode)
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hn : t.locals.lookup (ofString "nlen") = some (.val (.word NL))) :
    Reaches t (.seq midCheck cont)
      (fun E => SszCheckOffsetsReturned t offsets 3 44 NL (.val (.word 0)) ∧ E.memory = t.memory ∧
        E.globals = t.globals ∧ E.memaddrs = t.memaddrs ∧ E.locals = t.locals ∧ E.code = t.code) 8 cont := by
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      [stOffsetsGlobal, .const 3, .const 44, sszLocal "nlen"] =
      some [.val (.word offsets), .val (.word 3), .val (.word 44), .val (.word NL)] := by
    simp [stOffsetsGlobal, sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, hg, hn]
  have lower := evaluateHOLFiniteState_clock_le t midCheck
  have nr := evaluate_discard_call_no_return t (ofString "ssz_check_offsets")
    [stOffsetsGlobal, .const 3, .const 44, sszLocal "nlen"]
  apply reaches_seq
  cases run : evaluateHOLFiniteState t midCheck with
  | mk r E =>
    rw [run] at lower
    replace lower : E.clock ≤ t.clock := lower
    have bounded : 8 ≤ t.clock → t.clock ≤ E.clock + 8 ∧ r ≠ some .timeOut := by
      intro en
      have b := evaluate_sszCheckOffsets_call_bounded t none _ offsets 3 44 NL args code (by decide) en
      unfold midCheck at run; rw [run] at b
      exact ⟨b.1, b.2.2⟩
    have clockBound : t.clock ≤ E.clock + 8 := by
      by_cases en : 8 ≤ t.clock
      · exact (bounded en).1
      · omega
    cases r with
    | none =>
      obtain ⟨checked, em, eg, ed, el⟩ := sszCheckOffsets_call_returned t _ offsets 3 44 NL args code (by decide) E
        (by unfold midCheck at run; exact run)
      have mt := evaluateHOLFiniteState_metadata t midCheck
      rw [run] at mt
      exact Or.inl ⟨E, ⟨checked, em, eg, ed, el, mt.1⟩, clockBound, lower, rfl⟩
    | some x =>
      right
      exact ⟨x, rfl, fun v h => nr v (by unfold midCheck at run; rw [run, h]), clockBound, lower,
        fun en h => (bounded en).2 (by rw [h])⟩

#print axioms reaches_alloc96
#print axioms reaches_midCheck
end InitECandidate.Runtime
