import InitECandidate.Proofs.Op5.FullInitArena
import Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
open Flapjack.Pancake

theorem impInitStateOkWithArena {width : Nat} [NeZero width] {C F : Type} {kkk : Nat}
    {bitmaps t : List (BitVec width)}
    {wordOracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    {stackOracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {ac : AsmConfigExact width} {scc : StackToLab.Config} {dc : DataToWord.Config}
    {maxHeap stk : Nat} {stoff : BitVec width × BitVec width} {p6 : List (Nat × HolProg width)}
    {labSt : LabSem.State width C F} {saveRegs : Nat → Bool} {dataSp : Nat}
    {arena : BitVec width → Prop}
    {fmis xxx : StackSemStateFiniteExact width C F} :
    4 < kkk ∧ bitmaps = 4 :: t ∧ goodDimindex width ∧
      (∀ n,
        let ((bm0, _), progs) := wordOracle n
        progs.all (fun p => postAllocConventionsHOL kkk p.2.2) = true ∧
        progs.all (fun p => flatExpConventions p.2.2) = true ∧
        progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
        progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
        (n = 0 → bm0 = bitmaps.length)) ∧
      stackOracle = (fun n =>
        let ((bm0, cfg), progs) := wordOracle n
        let (progs, _, bm) := compileWordToStackNative ac false kkk progs (.nil, bm0)
        (cfg, progs, appListAppend bm.1)) ∧
      fullMakeInitWithArena scc dc maxHeap stk stoff bitmaps p6 labSt saveRegs dataSp stackOracle arena =
        (fmis, some xxx) →
      WordToStackProofs.InitializationStateRel.initStateOk ac kkk fmis wordOracle := by
  rintro ⟨hk, rfl, hdim, hconv, horacle, hf⟩
  simp only [fullMakeInitWithArena, Prod.mk.injEq] at hf
  obtain ⟨hfmis, hopt⟩ := hf
  subst hfmis
  unfold makeInitAnyWithArena
  rw [hopt]
  obtain ⟨cur, oth, bb, len, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ :=
    (makeInitOptWithArena_eq_some hopt).choose_spec.2
  obtain ⟨t', rfl, _⟩ := makeInitOptWithArena_eq_some hopt
  simp only [StackAlloc.makeInit, WordToStackProofs.InitializationStateRel.initStateOk]
  refine ⟨hk, hdim, by rcases hdim with h | h <;> omega, trivial, h22, trivial,
    DataToWord.Proofs.Gc.gcFunOkWordGcFun, by omega, h23, ?_, ?_,
    h25, drop_eq_singleton_of_holLast _ _ _ h29 h28, Option.ne_none_iff_exists'.mpr ⟨_, h12⟩,
    ?_, horacle, ?_⟩
  all_goals simp only [initReduceWithArena, withArena, StackRemove.Proofs.InitReduce.initReduce] at h24 ⊢
  · simp at h24 ⊢; omega
  · exact ⟨t, rfl⟩
  · simp at h24 ⊢; omega
  · intro n
    simpa [ne_comm] using hconv n

#print axioms impInitStateOkWithArena
end InitE.Op5
