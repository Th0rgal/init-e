import InitECandidate.Runtime.LabWeightedClock
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

/-- Embed an ordinary prefix in the event-aware execution model without
changing its cost. -/
theorem WeightedInstructionTrace.toMixed {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : WeightedInstructionTrace code start final work) :
    WeightedMixedTrace code start final work := by
  simpa only [Nat.add_zero] using WeightedMixedTrace.ordinary start final final work 0 trace (.nil final)

/-- Clock extension preserves the actual sequence of ordinary, FFI and shared
operations, with unchanged per-event costs and state effects. -/
theorem WeightedMixedTrace.add_clock {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : WeightedMixedTrace code start final work) (k : Nat) :
    WeightedMixedTrace code {start with clock := start.clock + k}
      {final with clock := final.clock + k} work := by
  induction trace with
  | nil state => exact .nil _
  | ordinary start middle final length restLength segment rest ih =>
    exact .ordinary _ _ _ _ _ (segment.add_clock k) ih
  | ffi state final name w bytes n len ptr len2 ptr2 conf bytes2 n1 n2 newPc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    refine WeightedMixedTrace.ffi _ _ name w bytes n len ptr len2 ptr2 conf bytes2 n1 n2 newPc
      newFfi newBytes length ?_ fetch hlen hptr hlen2 hptr2 read1 read2 link destination call ?_
    · show state.clock + k ≠ 0; omega
    · have successor : ffiReturnedSource {state with clock := state.clock + k}
          name ptr2 newBytes newPc newFfi =
          {ffiReturnedSource state name ptr2 newBytes newPc newFfi with
            clock := (ffiReturnedSource state name ptr2 newBytes newPc newFfi).clock + k} := by
        simp only [ffiReturnedSource]
        congr 1
        omega
      rw [successor]
      exact ih
  | shared state final operator register base offset bytes n ffi returned next length
      clock fetch operation rest ih =>
    have shifted := (LabProps.shareMemOpAddClockSame state operator register (.addr base offset) k
      ffi returned next {name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed}
      state).2.1 ⟨clock, operation⟩
    rw [Nat.add_comm k state.clock, Nat.add_comm k next.clock] at shifted
    refine WeightedMixedTrace.shared _ _ operator register base offset bytes n ffi returned
      {next with clock := next.clock + k} length ?_ fetch shifted ?_
    · show state.clock + k ≠ 0; omega
    · exact ih

/-- Compiler ABI register indices and installed code survive ordinary work. -/
theorem WeightedInstructionTrace.metadata {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : WeightedInstructionTrace code start final work) :
    final.code = start.code ∧ final.ptrReg = start.ptrReg ∧
      final.lenReg = start.lenReg ∧ final.ptr2Reg = start.ptr2Reg ∧
      final.len2Reg = start.len2Reg ∧ final.linkReg = start.linkReg := by
  induction trace with
  | step state final instruction bytes n length clock fetch success rest ih =>
    obtain ⟨_, code, _, _, _, _, _, _, ptr, len, ptr2, len2, link⟩ := asmInstConsts instruction state
    simpa only [incPc, decClock, code, ptr, len, ptr2, len2, link] using ih
  | _ => simp_all only [incPc, decClock, LabSem.updPc, LabSem.updReg, and_self]

private def compilerMetadata {F : Type} (state : LabSem.State 64 LabToTarget.Config F) :=
  (state.code, state.ptrReg, state.lenReg, state.ptr2Reg, state.len2Reg, state.linkReg)

private theorem shared_return_metadata {F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr 64)
    (state next : LabSem.State 64 LabToTarget.Config F) (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (operation : shareMemOp operator register address state = some (.ret ffi bytes, next)) :
    compilerMetadata next = compilerMetadata state := by
  cases operator <;> simp only [shareMemOp] at operation
  all_goals first | unfold shareMemLoad at operation | unfold shareMemStore at operation
  all_goals repeat' first | split at operation | simp_all [incPc, decClock, compilerMetadata]
  all_goals simpa only [compilerMetadata, Prod.mk.injEq] using (congrArg compilerMetadata operation.2).symm

/-- Returned host operations may update register values, memory and FFI state;
the compiler ABI indices and installed code remain available for composition. -/
theorem WeightedMixedTrace.metadata {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : WeightedMixedTrace code start final work) :
    final.code = start.code ∧ final.ptrReg = start.ptrReg ∧
      final.lenReg = start.lenReg ∧ final.ptr2Reg = start.ptr2Reg ∧
      final.len2Reg = start.len2Reg ∧ final.linkReg = start.linkReg := by
  induction trace with
  | nil state => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ordinary start middle final length restLength segment rest ih =>
    obtain ⟨code, ptr, len, ptr2, len2, link⟩ := segment.metadata
    simpa only [code, ptr, len, ptr2, len2, link] using ih
  | ffi => simpa only [ffiReturnedSource] using (by assumption)
  | shared state final operator register base offset bytes n ffi returned next length
      clock fetch operation rest ih =>
    have same := shared_return_metadata operator register (.addr base offset) state next ffi returned operation
    simp only [compilerMetadata, Prod.mk.injEq] at same
    obtain ⟨code, ptr, len, ptr2, len2, link⟩ := same
    simpa only [code, ptr, len, ptr2, len2, link] using ih

#print axioms WeightedInstructionTrace.toMixed
#print axioms WeightedMixedTrace.add_clock
#print axioms WeightedInstructionTrace.metadata
#print axioms WeightedMixedTrace.metadata
end InitECandidate.Runtime.LabToTarget
