import InitECandidate.Runtime.RlpValidationStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every saved continuation record lies below the initial scratch ceiling. -/
def RlpValidationStackCeiling (ceiling : Nat) (frames : List RlpValidationFrame) : Prop :=
  ∀ saved ∈ frames, saved.record.toNat + 24 ≤ ceiling

theorem RlpValidationStackCeiling.tail {ceiling : Nat} {saved : RlpValidationFrame}
    {rest : List RlpValidationFrame} (bounded : RlpValidationStackCeiling ceiling (saved :: rest)) :
    RlpValidationStackCeiling ceiling rest := by
  intro record member
  exact bounded record (List.mem_cons_of_mem saved member)

/-- Allocating downward retains a fixed upper arena bound for all saved records. -/
theorem RlpValidationStackCeiling.push {ceiling : Nat} {frames : List RlpValidationFrame}
    (bounded : RlpValidationStackCeiling ceiling frames) (scratch resume stop : BitVec 64)
    (fits : 24 ≤ scratch.toNat) (below : scratch.toNat ≤ ceiling) :
    RlpValidationStackCeiling ceiling
      ({record := scratchAllocationEnd scratch 24,resume := resume,stop := stop} :: frames) := by
  intro saved member
  rcases List.mem_cons.mp member with equal | previous
  · subst saved
    have before := scratchAllocationEnd_before scratch 24 fits
    change (scratchAllocationEnd scratch 24).toNat + 24 ≤ scratch.toNat at before
    exact before.trans below
  · exact bounded saved previous

/-- Stack layout and a fixed readable arena imply readability of all three
fields of every saved continuation, including records above the current frontier. -/
theorem RlpValidationStack.readable {F : Type} (state : PanSemStateFiniteExact 64 F)
    {frontier ceiling : Nat} {frames : List RlpValidationFrame}
    (valid : RlpValidationStack state.memory frontier frames)
    (bounded : RlpValidationStackCeiling ceiling frames)
    (arena : ∀ address : BitVec 64, frontier ≤ address.toNat → address.toNat < ceiling → state.memaddrs address) :
    ∀ saved ∈ frames, state.memaddrs saved.record ∧
      state.memaddrs (saved.record + 8) ∧ state.memaddrs (saved.record + 16) := by
  induction valid with
  | nil => simp
  | cons saved rest nonzero above recordBound resume stop link tail ih =>
    intro record member
    rcases List.mem_cons.mp member with equal | previous
    · subst record
      have upper := bounded saved (by simp)
      have field : ∀ offset : Nat, offset < 24 → state.memaddrs (saved.record + BitVec.ofNat 64 offset) := by
        intro offset inside
        have noWrap : saved.record.toNat + (BitVec.ofNat 64 offset).toNat < 2^64 := by
          rw [BitVec.toNat_ofNat]
          have small : offset < 2^64 := by omega
          rw [Nat.mod_eq_of_lt small]
          omega
        apply arena
        · rw [BitVec.toNat_add_of_lt noWrap]; omega
        · rw [BitVec.toNat_add_of_lt noWrap,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset < 2^64 by omega)]
          omega
      exact ⟨by simpa using field 0 (by decide),field 8 (by decide),field 16 (by decide)⟩
    · exact ih bounded.tail record previous

#print axioms RlpValidationStackCeiling.push
#print axioms RlpValidationStack.readable
end InitECandidate.Runtime
