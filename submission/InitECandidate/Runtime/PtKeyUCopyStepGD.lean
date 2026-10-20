import InitECandidate.Runtime.MemcpyByteSuffixMemory
import InitECandidate.Runtime.PtKeyUMemeqStepGD
/-!
Byte-copy steps (`st8 (dst + i + k), ld8 (src + i + k)` …, then `i = i + c`) whose loads and stores all address
addressable aligned cells: no error, the counter advances, and memory changes only in the destination's cells.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cs
variable {F : Type}

/-- A byte store whose address and value evaluate, into an addressable cell, succeeds and changes only that cell. -/
theorem evaluate_storeByte_ok (state : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a w : BitVec 64)
    (hd : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) d =
      some (.val (.word a)))
    (hv : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) v =
      some (.val (.word w)))
    (dom : state.memaddrs (panByteAlignHOL a)) :
    ∃ M' : BitVec 64 → HolWordLab 64, evaluateHOLFiniteState state (.storeByte d v) = (none, {state with memory := M'}) ∧
      ∀ x, x ≠ panByteAlignHOL a → M' x = state.memory x := by
  obtain ⟨cell, hc⟩ : ∃ c : BitVec 64, state.memory (panByteAlignHOL a) = .word c := by
    cases state.memory (panByteAlignHOL a) with | word c => exact ⟨c, rfl⟩
  rw [evaluateHOLFiniteState_storeByte, hd, hv]
  simp only [panMemStoreByteWord8HOL, hc, dom, if_true]
  refine ⟨_, rfl, ?_⟩
  intro x hx
  simp [hx]

/-- The store/value pairs of a byte-copy step, in order. -/
def bsStores : ProgHOL 64 → List (ExpHOL 64 × ExpHOL 64)
  | .seq (.storeByte d v) rest => (d, v) :: bsStores rest
  | _ => []

/-- The step has no scoped temporaries. -/
def bsNoDec : ProgHOL 64 → Bool
  | .seq (.storeByte _ _) rest => bsNoDec rest
  | .dec _ _ _ _ => false
  | _ => true

/-- A byte-copy step whose stores all succeed inside the write set `W`: it advances the counter, changes memory only
inside `W`, and keeps every other field. -/
theorem evaluate_copyStep_ok {counter : MlS} {increment : BitVec 64} {program : ProgHOL 64}
    (supported : ByteAdvanceStep counter increment program) (W : BitVec 64 → Prop)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (D : BitVec 64 → Prop)
    (ok : ∀ (t : PanSemStateFiniteExact 64 F), t.locals = L → t.memaddrs = D → ∀ p ∈ bsStores program,
      ∃ a w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address)) p.1 =
        some (.val (.word a)) ∧
      @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address)) p.2 =
        some (.val (.word w)) ∧ D (panByteAlignHOL a) ∧ W (panByteAlignHOL a))
    (nodec : bsNoDec program = true)
    (state : PanSemStateFiniteExact 64 F) (hl : state.locals = L) (hd : state.memaddrs = D)
    (index : BitVec 64) (binding : state.locals.lookup counter = some (.val (.word index))) :
    ∃ M' : BitVec 64 → HolWordLab 64, evaluateHOLFiniteState state program =
      (none, setVarHOLFinite counter (.val (.word (index + increment))) {state with memory := M'}) ∧
      ∀ x, ¬ W x → M' x = state.memory x := by
  induction supported generalizing state with
  | advance =>
    refine ⟨state.memory, ?_, fun _ _ => rfl⟩
    apply evaluate_local_word_assignment state counter _ index (index + increment) binding
    simp [evalHOLExact, evalListHOLExact, binding, wordOpHOL, wordOp, valueIsWord, valueWord]
  | store d v tail ih =>
    obtain ⟨a, w, ea, ew, da, wa⟩ := ok state hl hd (d, v) (by simp [bsStores])
    obtain ⟨M1, run1, fr1⟩ := evaluate_storeByte_ok state d v a w ea ew (by rw [hd]; exact da)
    have ok' : ∀ (t : PanSemStateFiniteExact 64 F), t.locals = L → t.memaddrs = D → ∀ p ∈ bsStores _,
        ∃ a w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address)) p.1 =
          some (.val (.word a)) ∧
        @evalHOLExact 64 F _ t.toExact (fun address => Classical.propDecidable (t.memaddrs address)) p.2 =
          some (.val (.word w)) ∧ D (panByteAlignHOL a) ∧ W (panByteAlignHOL a) :=
      fun t h1 h2 p hp => ok t h1 h2 p (by simp only [bsStores, List.mem_cons]; exact Or.inr hp)
    obtain ⟨M2, run2, fr2⟩ := ih ok' (by simpa [bsNoDec] using nodec) {state with memory := M1} hl hd binding
    refine ⟨M2, ?_, ?_⟩
    · rw [evaluateHOLFiniteState_seq_line780, run1]
      exact run2
    · intro x hx
      rw [fr2 x hx]
      exact fr1 x (fun h => hx (h ▸ wa))
  | declare name initializer different nested ih =>
    simp [bsNoDec] at nodec

end cs
#print axioms evaluate_storeByte_ok
#print axioms evaluate_copyStep_ok
end InitECandidate.Runtime
