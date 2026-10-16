import InitECandidate.Runtime.StackEntryBudget
import Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend

/-- The renamed final halting stub is a sequence of one instruction and halt. -/
theorem haltStub_work {width : Nat} [NeZero width] {C F : Type}
    (names : Spt Nat) (s : StackSemStateFiniteExact width C F) :
    stackWork (StackNames.progCompHOL names (StackRemove.haltInst (0 : BitVec width))) s = 6 := by
  simp [StackRemove.haltInst, StackNames.progCompHOL, stackWork]

/-- Compiler initialization installs the same fixed procedure at label 1. -/
theorem compiled_halt_lookup {width : Nat} [NeZero width]
    (names : Spt Nat) (jump : Bool) (offset : BitVec width × BitVec width)
    (gen : Bool) (maxHeap sp start : Nat) (code : List (Nat × HolProg width)) :
    sptLookup 1 (sptFromAList (StackNames.compileHOL names
      (StackRemove.compileHOL jump offset gen maxHeap sp start code))) =
      some (StackNames.progCompHOL names (StackRemove.haltInst (0 : BitVec width))) := by
  simp [sptLookup_sptFromAList, StackNames.compileHOL, StackRemove.compileHOL,
    StackRemove.initStubs, StackNames.progCompEntryHOL, sptAListLookup]

/-- A returned location 1 uses the fixed halting stub, including after code
extensions during evaluation. Its budget does not depend on memory or clock. -/
theorem entryWork_return_one {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s final : StackSemStateFiniteExact width C F)
    (prog : HolProg width) (names : Spt Nat)
    (entry : sptLookup start s.code = some prog)
    (stub : sptLookup 1 s.code =
      some (StackNames.progCompHOL names (StackRemove.haltInst (0 : BitVec width))))
    (run : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s) =
      (some (.result (.loc 1 0)), final)) :
    entryWork start s = stackWork prog (StackSemStateOps.decClock s) + 6 := by
  have extension := (StackProps.EvaluateMono.evaluateMono _ _ _ _ run).2
  have initialMem : sptMem 1 (StackSemStateOps.decClock s).code :=
    (sptMem_iff_lookup _ _).2 ⟨_, stub⟩
  have finalStub := (extension 1 initialMem).2
  simp only [StackSemStateOps.decClock] at finalStub
  rw [stub] at finalStub
  simp only [entryWork, entry, run, finalStub, haltStub_work]

#print axioms compiled_halt_lookup
#print axioms haltStub_work
#print axioms entryWork_return_one
end InitECandidate.Runtime.StackToLab
