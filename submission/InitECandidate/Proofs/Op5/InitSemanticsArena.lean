import InitECandidate.Proofs.Op5.MakeInitArena
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
open Flapjack.Compiler.Backend.StackLang

/-- The entry bootstrap is independent of the shape of the ordinary domain.
The unchanged initializer's actual successful run and FFI preservation imply
clock-indexed semantic equality for its entry wrapper. -/
theorem initializer_entry_semantics {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap pointer start : Nat)
    (s t : StackSemStateFiniteExact width C F)
    (entry : sptLookup 0 s.code =
      some (.seq (initCode gc maxHeap pointer) (.call none (.inl start) none)))
    (run : StackSemEvaluate.evaluate (initCode gc maxHeap pointer,s) = (none,t))
    (ffi : t.ffi = s.ffi) :
    StackSemEvaluate.semantics 0 s = StackSemEvaluate.semantics start t := by
  rw [StackSemEvaluate.semantics_eq_aux, StackSemEvaluate.semantics_eq_aux]
  apply semanticsAux_shift
  · rw [StackSemEvaluate.evaluate_call]
    simp [StackSemControl.findCode, entry]
  · rw [callZeroFfi _ _ rfl, callZeroFfi _ _ rfl]
    exact ffi.symm
  · intro k
    have clockRun := InitClock.evaluateInitCodeClock gc maxHeap pointer s t none k run
    have body : StackSemEvaluate.evaluate (.seq (initCode gc maxHeap pointer)
        (.call none (.inl start) none), {s with clock := k}) =
        StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := k}) := by
      rw [StackSemEvaluate.evaluate_seq, clockRun]
      simp [StackSemControl.fixClock]
    have notBad := callNotBad start {t with clock := k}
    rw [StackSemEvaluate.evaluate_call]
    simp only [StackSemControl.findCode, entry, Nat.add_one_ne_zero, if_false,
      StackSemStateOps.decClock, Nat.add_sub_cancel]
    rw [show ({ ({s with clock := k + 1} : StackSemStateFiniteExact width C F) with
        clock := k } : StackSemStateFiniteExact width C F) = {s with clock := k} from rfl, body]
    simp only [StackSemControl.fixClock, notBad]
    exact ⟨rfl, rfl⟩

/-- End-to-end StackRemove initialization and compiler simulation with scratch:
the extended initialized state has the same non-failing observable semantics
as the unchanged compiled entry code. -/
theorem makeInitOptWithArena_semantics {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap pointer start : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (s : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop)
    (jump : Bool) (bounds : BitVec width × BitVec width) (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (entry : sptLookup 0 s.code =
      some (.seq (initCode gc maxHeap pointer) (.call none (.inl start) none)))
    (pre : initCodePreWithArena pointer bitmaps dataSpace s arena)
    (codeRel : codeRelHOL jump bounds pointer code s.code)
    (oracleEq : s.compileOracle = fun i =>
      let e := oracle i
      (e.1,e.2.1.map (progComp jump bounds pointer),e.2.2))
    (oracleBound : ∀ n i p, (i,p) ∈ (oracle n).2.1 →
      Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i+1)
    (err : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)))
    (maxOk : maxStackAlloc ≤ maxHeap) :
    ∃ r, makeInitOptWithArena gc maxHeap bitmaps dataSpace oracle jump bounds pointer code s arena = some r ∧
      (StackSemEvaluate.semantics start r ≠ HolBehaviour.fail →
        StackSemEvaluate.semantics 0 s = StackSemEvaluate.semantics start r) := by
  obtain ⟨r,t,opt,run,rel,ffi,_⟩ := makeInitOptWithArena_correct gc maxHeap pointer bitmaps
    dataSpace s arena jump bounds code oracle pre codeRel oracleEq oracleBound err maxOk
  refine ⟨r,opt,?_⟩
  intro notFail
  rw [initializer_entry_semantics gc maxHeap pointer start s t entry run ffi]
  exact CompileSemantics.compileSemantics jump bounds pointer start r t ⟨rel,notFail⟩

#print axioms initializer_entry_semantics
#print axioms makeInitOptWithArena_semantics
end InitE.Op5
