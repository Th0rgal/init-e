import InitECandidate.Runtime.MemzeroWordCoverage
import InitECandidate.Runtime.MemzeroWord8Loop
import InitECandidate.Runtime.MemzeroMemoryFrameStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original eight-byte zero loop terminates within the remaining-byte
budget, retaining tail clocks and preserving a separate watched memory word. -/
theorem evaluate_memzero_word8_frame_loop {F : Type} (destination size watched : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ (state : PanSemStateFiniteExact 64 F) (index : BitVec 64),
      state.locals.lookup (ofString "dst") = some (.val (.word destination)) →
      state.locals.lookup (ofString "n") = some (.val (.word size)) →
      state.locals.lookup (ofString "i") = some (.val (.word index)) →
      index.toNat ≤ size.toNat → size.toNat - index.toNat = rank → rank ≤ state.clock →
      (∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset)) →
      (∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset) →
      ∃ post finalIndex, evaluateHOLFiniteState state memzeroWord8Loop = (none,post) ∧
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8 ∧
        post.memory watched = state.memory watched ∧
        state.clock + (size.toNat - finalIndex.toNat) ≤ post.clock + rank ∧ post.clock ≤ state.clock ∧
        post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  classical
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state index dstLocal sizeLocal indexLocal inside distance budget domain separate
    have addBound : index.toNat + (8 : BitVec 64).toNat < 2 ^ 64 := by
      change index.toNat + 8 < 2 ^ 64
      omega
    have advanced := BitVec.toNat_add_of_lt addBound
    have advancedNat : (index + 8).toNat = index.toNat + 8 := advanced
    have condition := eval_memzero_block_condition state index size 8 indexLocal sizeLocal
    by_cases guard : index.toNat + 8 ≤ size.toNat
    · have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (index + 8) = true := by
        change (!decide (size.toNat < (index + 8).toNat)) = true
        have bound : (index + 8).toNat ≤ size.toNat := by rw [advancedNat]; exact guard
        rw [decide_eq_false (Nat.not_lt.mpr bound)]
        rfl
      obtain ⟨next,body,ticks,nextIndex,globals,code,addresses,endian,locals,bodyFrame⟩ :=
        evaluate_memzero_word8_frame_step (decClockHOLFinite state) destination index watched dstLocal indexLocal
          (by change state.memaddrs (destination + index); simpa using domain index.toNat (by omega))
          (by simpa using separate index.toNat (by omega))
      have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word destination)) :=
        (locals _ (by decide)).trans dstLocal
      have nextSize : next.locals.lookup (ofString "n") = some (.val (.word size)) :=
        (locals _ (by decide)).trans sizeLocal
      have nextDomain : ∀ offset : Nat, offset < size.toNat → next.memaddrs (destination + BitVec.ofNat 64 offset) := by
        intro offset bound; rw [addresses]; exact domain offset bound
      have decreases : size.toNat - (index + 8).toNat < rank := by rw [advancedNat]; omega
      obtain ⟨post,finalIndex,tail,finalLocal,finalBound,remainder,finalCount,cost,remaining,
        finalGlobals,finalCode,finalDomain,finalEndian,otherLocals⟩ := ih _ decreases next (index + 8)
        nextDst nextSize nextIndex (by rw [advancedNat]; exact guard) rfl
        (by change next.clock = state.clock - 1 at ticks; rw [advancedNat]; omega)
        nextDomain separate
      have run : evaluateHOLFiniteState state memzeroWord8Loop = evaluateHOLFiniteState next memzeroWord8Loop := by
        unfold memzeroWord8Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        rw [flag]
        simp only [if_true]
        have clockNonzero : state.clock ≠ 0 := by omega
        simp [clockNonzero,body,fixClockHOLFinite]
        have equalClock : (decClockHOLFinite state).clock = next.clock := ticks.symm
        rw [equalClock]
        simp
      refine ⟨post,finalIndex,run.trans tail,finalLocal,finalBound,remainder,finalCount.trans bodyFrame,?_,?_,
        finalGlobals.trans globals,finalCode.trans code,finalDomain.trans addresses,finalEndian.trans endian,?_⟩
      · change next.clock = state.clock - 1 at ticks
        rw [advancedNat] at cost
        omega
      · change next.clock = state.clock - 1 at ticks
        omega
      · intro name different
        exact (otherLocals name different).trans (locals name different)
    · have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (index + 8) = false := by
        change (!decide (size.toNat < (index + 8).toNat)) = false
        have bound : size.toNat < (index + 8).toNat := by rw [advancedNat]; omega
        rw [decide_eq_true bound]
        rfl
      have run : evaluateHOLFiniteState state memzeroWord8Loop = (none,state) := by
        unfold memzeroWord8Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        rw [flag]
        simp
      exact ⟨state,index,run,indexLocal,inside,by omega,rfl,by omega,by omega,rfl,rfl,rfl,rfl,by intro name different; rfl⟩

#print axioms evaluate_memzero_word8_frame_loop
end InitECandidate.Runtime
