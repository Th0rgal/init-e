import InitECandidate.Runtime.MemzeroByteCoverage
import InitECandidate.Runtime.MemzeroByte1Loop
import InitECandidate.Runtime.MemzeroMemoryFrameStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original final-byte zero loop terminates in exactly one guard clock
per remaining byte and preserves a separate memory word and other locals. -/
theorem evaluate_memzero_byte1_frame_loop {F : Type} (destination size watched : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ (state : PanSemStateFiniteExact 64 F) (index : BitVec 64),
      state.locals.lookup (ofString "dst") = some (.val (.word destination)) →
      state.locals.lookup (ofString "n") = some (.val (.word size)) →
      state.locals.lookup (ofString "i") = some (.val (.word index)) →
      index.toNat ≤ size.toNat → size.toNat - index.toNat = rank → rank ≤ state.clock →
      (∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) →
      (∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
      ∃ post, evaluateHOLFiniteState state memzeroByte1Loop = (none,post) ∧
        post.locals.lookup (ofString "i") = some (.val (.word size)) ∧ post.memory watched = state.memory watched ∧
        post.clock = state.clock - rank ∧ post.globals = state.globals ∧ post.code = state.code ∧
        post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  classical
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state index dstLocal sizeLocal indexLocal inside distance budget domain separate
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
          some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .lower index size then 1 else 0))) := by
      simp only [evalHOLExact]
      rw [indexLocal,sizeLocal]
    by_cases guard : index.toNat < size.toNat
    · have flag : Compiler.Encoders.Asm.wordCmpHOL .lower index size = true := by
        change decide (index.toNat < size.toNat) = true
        exact decide_eq_true guard
      obtain ⟨next,body,ticks,nextIndex,globals,code,addresses,endian,locals,bodyFrame⟩ :=
        evaluate_memzero_byte1_frame_step (decClockHOLFinite state) destination index watched dstLocal indexLocal
          (by change state.memaddrs (panByteAlignHOL (destination + index)); simpa using domain index.toNat guard)
          (by simpa using separate index.toNat guard)
      have advancedNat : (index + 1).toNat = index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2^64; omega)]
        rfl
      have nextDst := (locals (ofString "dst") (by decide)).trans dstLocal
      have nextSize := (locals (ofString "n") (by decide)).trans sizeLocal
      have nextDomain : ∀ offset : Nat, offset < size.toNat → next.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
        intro offset bound; rw [addresses]; exact domain offset bound
      have decreases : size.toNat - (index + 1).toNat < rank := by rw [advancedNat]; omega
      obtain ⟨post,tail,finalIndex,finalCount,finalClock,finalGlobals,finalCode,finalDomain,finalEndian,otherLocals⟩ :=
        ih _ decreases next (index + 1) nextDst nextSize nextIndex (by rw [advancedNat]; omega) rfl
          (by change next.clock = state.clock - 1 at ticks; rw [advancedNat]; omega) nextDomain separate
      have run : evaluateHOLFiniteState state memzeroByte1Loop = evaluateHOLFiniteState next memzeroByte1Loop := by
        unfold memzeroByte1Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,flag]
        simp only [if_true]
        have clockNonzero : state.clock ≠ 0 := by omega
        simp [clockNonzero,body,fixClockHOLFinite]
        have equalClock : (decClockHOLFinite state).clock = next.clock := ticks.symm
        rw [equalClock]
        simp
      refine ⟨post,run.trans tail,finalIndex,finalCount.trans bodyFrame,?_,finalGlobals.trans globals,finalCode.trans code,
        finalDomain.trans addresses,finalEndian.trans endian,?_⟩
      · change next.clock = state.clock - 1 at ticks
        rw [advancedNat] at finalClock
        omega
      · intro name different
        exact (otherLocals name different).trans (locals name different)
    · have flag : Compiler.Encoders.Asm.wordCmpHOL .lower index size = false := by
        change decide (index.toNat < size.toNat) = false
        exact decide_eq_false guard
      have same : index = size := BitVec.eq_of_toNat_eq (by omega)
      have run : evaluateHOLFiniteState state memzeroByte1Loop = (none,state) := by
        unfold memzeroByte1Loop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,flag]
        simp
      subst index
      exact ⟨state,run,indexLocal,rfl,by omega,rfl,rfl,rfl,rfl,by intro name different; rfl⟩

#print axioms evaluate_memzero_byte1_frame_loop
end InitECandidate.Runtime
