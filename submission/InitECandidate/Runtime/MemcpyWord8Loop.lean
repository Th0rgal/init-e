import InitECandidate.Runtime.MemzeroWordCoverage
import InitECandidate.Runtime.MemcpyWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyWord8Loop : ProgHOL 64 := .while (memzeroBlockCondition 8) memcpyWord8Body

/-- The original eight-byte copy loop terminates within the remaining-byte
budget, retaining tail clocks and preserving a separate occupancy array. -/
theorem evaluate_memcpy_word8_loop {F : Type} (destination source size capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ (state : PanSemStateFiniteExact 64 F) (index : BitVec 64),
      state.locals.lookup (ofString "dst") = some (.val (.word destination)) →
      state.locals.lookup (ofString "src") = some (.val (.word source)) →
      state.locals.lookup (ofString "n") = some (.val (.word size)) →
      state.locals.lookup (ofString "i") = some (.val (.word index)) →
      index.toNat ≤ size.toNat → size.toNat - index.toNat = rank → rank ≤ state.clock →
      (∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset)) →
      (∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset)) →
      (∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset) →
      ∃ post finalIndex, evaluateHOLFiniteState state memcpyWord8Loop = (none,post) ∧
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8 ∧
        hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
        state.clock + (size.toNat - finalIndex.toNat) ≤ post.clock + rank ∧ post.clock ≤ state.clock ∧
        post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  classical
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state index dstLocal srcLocal sizeLocal indexLocal inside distance budget domain sourceDomain separate
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
      obtain ⟨next,body,ticks,nextIndex,globals,code,addresses,endian,locals,counts⟩ :=
        evaluate_memcpy_word8_step (decClockHOLFinite state) destination source index dstLocal srcLocal indexLocal
          (by change state.memaddrs (destination + index); simpa using domain index.toNat (by omega))
          (by change state.memaddrs (source + index); simpa using sourceDomain index.toNat (by omega))
      have count := counts capacity used (by simpa using separate index.toNat (by omega))
      have nextSrc : next.locals.lookup (ofString "src") = some (.val (.word source)) :=
        (locals _ (by decide)).trans srcLocal
      have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word destination)) :=
        (locals _ (by decide)).trans dstLocal
      have nextSize : next.locals.lookup (ofString "n") = some (.val (.word size)) :=
        (locals _ (by decide)).trans sizeLocal
      have nextDomain : ∀ offset : Nat, offset < size.toNat → next.memaddrs (destination + BitVec.ofNat 64 offset) := by
        intro offset bound; rw [addresses]; exact domain offset bound
      have nextSourceDomain : ∀ offset : Nat, offset < size.toNat → next.memaddrs (source + BitVec.ofNat 64 offset) := by
        intro offset bound; rw [addresses]; exact sourceDomain offset bound
      have decreases : size.toNat - (index + 8).toNat < rank := by rw [advancedNat]; omega
      obtain ⟨post,finalIndex,tail,finalLocal,finalBound,remainder,finalCount,cost,remaining,
        finalGlobals,finalCode,finalDomain,finalEndian,otherLocals⟩ := ih _ decreases next (index + 8)
        nextDst nextSrc nextSize nextIndex (by rw [advancedNat]; exact guard) rfl
        (by change next.clock = state.clock - 1 at ticks; rw [advancedNat]; omega)
        nextDomain nextSourceDomain separate
      have run : evaluateHOLFiniteState state memcpyWord8Loop = evaluateHOLFiniteState next memcpyWord8Loop := by
        unfold memcpyWord8Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        rw [flag]
        simp only [if_true]
        have clockNonzero : state.clock ≠ 0 := by omega
        simp [clockNonzero,body,fixClockHOLFinite]
        have equalClock : (decClockHOLFinite state).clock = next.clock := ticks.symm
        rw [equalClock]
        simp
      refine ⟨post,finalIndex,run.trans tail,finalLocal,finalBound,remainder,finalCount.trans count,?_,?_,
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
      have run : evaluateHOLFiniteState state memcpyWord8Loop = (none,state) := by
        unfold memcpyWord8Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        rw [flag]
        simp
      exact ⟨state,index,run,indexLocal,inside,by omega,rfl,by omega,by omega,rfl,rfl,rfl,rfl,by intro name different; rfl⟩

#print axioms evaluate_memcpy_word8_loop
end InitECandidate.Runtime
