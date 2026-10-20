import InitECandidate.Runtime.HashFindLoopRank
/-!
Cyclic-rank induction for the source lookup loop with a per-probe cost `c` (≥ 2) instead of exactly two clocks:
probes whose key comparison runs the `memeq` byte loops spend between two and `c` clocks.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindLoop_rankC {F : Type}
    (capacity empty used : BitVec 64) (bits c : Nat) (hc : 2 ≤ c)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (invariant : PanSemStateFiniteExact 64 F → BitVec 64 → Prop)
    (bindings : ∀ state index, invariant state index →
      state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
      state.locals.lookup (ofString "used") = some (.val (.word used)))
    (readable : ∀ state index, invariant state index → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte)
    (emptyLoad : ∀ state index, invariant state index →
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + empty) = some 0)
    (step : ∀ state index byte, invariant state index → index.toNat < capacity.toNat → c ≤ state.clock →
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte →
      BitVec.ofNat 64 byte.toNat ≠ 0 →
      ∃ result post, evaluateHOLFiniteState state hashFindLoop =
          (match result with | none => evaluateHOLFiniteState post hashFindLoop | some _ => (result,post)) ∧
        (result = none ∨ result = some (.returned (.val (.word index)))) ∧
        post.clock ≤ state.clock ∧ state.clock ≤ post.clock + c ∧
        (result = none → invariant post (hashProbeNext index capacity)) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) :
    ∀ rank state index, invariant state index → index.toNat < capacity.toNat →
      hashProbeDistance capacity.toNat index.toNat empty.toNat = rank → c * rank ≤ state.clock →
      ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
        state.clock ≤ post.clock + c * rank ∧ post.clock ≤ state.clock ∧
        (result = none ∨ ∃ found : BitVec 64, found.toNat < capacity.toNat ∧
          result = some (.returned (.val (.word found)))) ∧
        (result = none → ∃ finalIndex, invariant post finalIndex) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state index valid inside distance budget
    obtain ⟨i,u⟩ := bindings state index valid
    obtain ⟨byte,loaded⟩ := readable state index valid
    by_cases zero : BitVec.ofNat 64 byte.toNat = (0 : BitVec 64)
    · have byteZero : byte = 0 := by
        apply UInt8.toNat.inj
        have limit := byte.toNat_lt_size
        change byte.toNat < 256 at limit
        have equal := congrArg BitVec.toNat zero
        simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show byte.toNat < 2 ^ 64 by omega)] using equal
      have run := evaluate_hashFind_empty state used index i u (by simpa only [byteZero] using loaded)
      exact ⟨none,state,run,by omega,Nat.le_refl _,Or.inl rfl,fun _ => ⟨index,valid⟩,rfl,rfl,rfl,rfl,rfl⟩
    · have different : index ≠ empty := by
        intro same
        rw [same,emptyLoad state index valid] at loaded
        have byteZero : byte = 0 := (Option.some.inj loaded).symm
        apply zero
        simp [byteZero]
      have naturalDifferent : index.toNat ≠ empty.toNat := by
        intro equal; exact different (BitVec.eq_of_toNat_eq equal)
      have smaller : hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat < rank := by
        rw [hashProbeNext_wrap index capacity bits power inside,← distance]
        exact hashProbeDistance_decreases _ _ _ inside emptyInside naturalDifferent
      have rankPositive : 1 ≤ rank := by omega
      have cBudget : c ≤ state.clock := by
        have := Nat.mul_le_mul_left c rankPositive; omega
      obtain ⟨result,next,run,outcome,lo,hi,nextValid,memory,globals,code,addresses,endian⟩ :=
        step state index byte valid inside cBudget loaded zero
      rcases outcome with continuing | returned
      · have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
          rw [hashProbeNext_toNat index capacity bits power inside]
          apply Nat.mod_lt
          rw [power]; exact Nat.two_pow_pos bits
        have nextBudget : c * hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat ≤ next.clock := by
          have h1 := Nat.mul_le_mul_left c (show hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat + 1 ≤ rank by omega)
          rw [Nat.mul_add, Nat.mul_one] at h1
          omega
        obtain ⟨finalResult,post,tail,cost,remaining,finalOutcome,finalInvariant,tailMemory,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
          ih _ smaller next (hashProbeNext index capacity) (nextValid continuing) nextInside rfl nextBudget
        rw [continuing] at run
        have h1 := Nat.mul_le_mul_left c (show hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat + 1 ≤ rank by omega)
        rw [Nat.mul_add, Nat.mul_one] at h1
        refine ⟨finalResult,post,run.trans tail,by omega,by omega,finalOutcome,finalInvariant,tailMemory.trans memory,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩
      · rw [returned] at run
        have := Nat.mul_le_mul_left c rankPositive
        exact ⟨_,next,run,by omega,by omega,Or.inr ⟨index,inside,rfl⟩,(by intro impossible; cases impossible),memory,globals,code,addresses,endian⟩

#print axioms evaluate_hashFindLoop_rankC
end InitECandidate.Runtime
