import InitECandidate.Runtime.HeaderWithdrawalLoopRuntime
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- **Fence preservation needs no encoder-specific domain proof**: every evaluation keeps `memaddrs`
(`evaluateHOLFiniteState_metadata`), so the fence of the entry state is the fence of any post state,
for every program and every outcome. No heap cap is needed. -/
theorem fence_preserved {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    {DF : Nat} (fence : Fence state.memaddrs DF) :
    Fence (evaluateHOLFiniteState state program).2.memaddrs DF := by
  rw [(evaluateHOLFiniteState_metadata state program).2.1]
  exact fence

/-- Every evaluation keeps the installed code, so a code fact at the entry state is a code fact at
the post state of any run. -/
theorem code_preserved {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.code = originalRuntimeCode := by
  rw [(evaluateHOLFiniteState_metadata state program).1]
  exact code


/-- **Wiring the actual invariant into the per-iteration bound.** If the loop invariant supplies the
heap pointer value with its cap, the fence, and the evaluated argument, then one statement-46
iteration is bounded by `encodeWithdrawalSourceCost DF + 1` from that state. The fence part is free by
`fence_preserved`; only the heap cap and the argument evaluation come from the invariant. -/
theorem wdSliceLoopBody_runBounded_of_invariant (DF : Nat)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (heapOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      ∃ heap : BitVec 64, state.globals.lookup (ofString "heap_ptr") =
        some (ValueHOL.val (HolWordLab.word heap)) ∧ heap.toNat ≤ 33806089496)
    (fenceOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      Fence state.memaddrs DF)
    (argsOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      ∃ argumentWord : BitVec 64,
        evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
            .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
          some [ValueHOL.val (HolWordLab.word argumentWord)])
    (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      encodeWithdrawalSourceCost DF + 1 ≤ state.clock →
      RunBounded state wdSliceLoopBody (encodeWithdrawalSourceCost DF + 1) := by
  intro F state w pstate code atCounter budget
  obtain ⟨heap, atHeap, heapCap⟩ := heapOf state pstate
  obtain ⟨argumentWord, args⟩ := argsOf state pstate
  exact wdSliceLoopBody_runBounded state argumentWord heap DF args code (fenceOf state pstate)
    smallDF bigDF atHeap heapCap budget

/-- **Statement-46 loop runtime bound from an invariant** — the loop lemma with the per-iteration
hypothesis discharged by `wdSliceLoopBody_runBounded_of_invariant`, so the only remaining obligation is
the invariant preservation across one iteration. -/
theorem wdSliceLoop_runBounded_of_invariant (DF : Nat) (nwd : BitVec 64)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (heapOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      ∃ heap : BitVec 64, state.globals.lookup (ofString "heap_ptr") =
        some (ValueHOL.val (HolWordLab.word heap)) ∧ heap.toNat ≤ 33806089496)
    (fenceOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      Fence state.memaddrs DF)
    (argsOf : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      ∃ argumentWord : BitVec 64,
        evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
            .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
          some [ValueHOL.val (HolWordLab.word argumentWord)])
    (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF)
    (keep : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 = none →
      P (evaluateHOLFiniteState state wdSliceLoopBody).2)
    (advance : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 = none →
      (evaluateHOLFiniteState state wdSliceLoopBody).2.locals.lookup (ofString "i") =
        some (.val (.word (w + 1#64))) ∧
      (evaluateHOLFiniteState state wdSliceLoopBody).2.code = state.code)
    (noContinue : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 ≠ some .continue)
    (decrease : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      P (decClockHOLFinite state))
    (atBound : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.locals.lookup (ofString "nwd") = some (.val (.word nwd)))
    (small : nwd.toNat + 1 < 2 ^ 63) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.code = originalRuntimeCode →
      ∀ I0 : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word I0)) →
      I0.toNat ≤ nwd.toNat + 1 → nwd.toNat - I0.toNat = n →
      n * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state wdSliceLoop).2.clock +
        n * ((encodeWithdrawalSourceCost DF + 1) + 1) ∧
        (evaluateHOLFiniteState state wdSliceLoop).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state wdSliceLoop).1 ≠ some .timeOut :=
  wdSliceLoop_runBounded DF nwd P
    (wdSliceLoopBody_runBounded_of_invariant DF P heapOf fenceOf argsOf smallDF bigDF)
    keep advance noContinue decrease atBound small

#print axioms wdSliceLoopBody_runBounded_of_invariant
#print axioms wdSliceLoop_runBounded_of_invariant
#print axioms fence_preserved
#print axioms code_preserved
end InitECandidate.Runtime
