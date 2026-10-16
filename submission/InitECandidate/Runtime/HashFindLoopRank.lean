import InitECandidate.Runtime.HashFindOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Cyclic-rank induction for the actual lookup loop, allowing a matching
return before the known empty slot. The step premise is an evaluator equality
for the original loop, with its two-clock cost and continuing invariant. -/
theorem evaluate_hashFindLoop_rank {F : Type}
    (capacity empty used : BitVec 64) (bits : Nat)
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
    (step : ∀ state index byte, invariant state index → index.toNat < capacity.toNat → 2 ≤ state.clock →
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte →
      BitVec.ofNat 64 byte.toNat ≠ 0 →
      ∃ result post, evaluateHOLFiniteState state hashFindLoop =
          (match result with | none => evaluateHOLFiniteState post hashFindLoop | some _ => (result,post)) ∧
        (result = none ∨ result = some (.returned (.val (.word index)))) ∧
        post.clock = state.clock - 2 ∧
        (result = none → invariant post (hashProbeNext index capacity))) :
    ∀ rank state index, invariant state index → index.toNat < capacity.toNat →
      hashProbeDistance capacity.toNat index.toNat empty.toNat = rank → 2 * rank ≤ state.clock →
      ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
        state.clock ≤ post.clock + 2 * rank ∧ post.clock ≤ state.clock ∧
        (result = none ∨ ∃ found : BitVec 64, found.toNat < capacity.toNat ∧
          result = some (.returned (.val (.word found)))) := by
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
      exact ⟨none,state,run,by omega,Nat.le_refl _,Or.inl rfl⟩
    · have different : index ≠ empty := by
        intro same
        rw [same,emptyLoad state index valid] at loaded
        have byteZero : byte = 0 := (Option.some.inj loaded).symm
        apply zero
        simp [byteZero]
      have enough := hashFind_rank_budget capacity index empty bits state.clock power inside emptyInside different
        (by rw [distance]; exact budget)
      have naturalDifferent' : index.toNat ≠ empty.toNat := by
        intro equal; exact different (BitVec.eq_of_toNat_eq equal)
      have rankPositive : 0 < rank := by
        unfold hashProbeDistance at distance
        split at distance <;> omega
      obtain ⟨result,next,run,outcome,ticks,nextValid⟩ := step state index byte valid inside enough.1 loaded zero
      rcases outcome with continuing | returned
      · have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
          rw [hashProbeNext_toNat index capacity bits power inside]
          apply Nat.mod_lt
          rw [power]; exact Nat.two_pow_pos bits
        have naturalDifferent : index.toNat ≠ empty.toNat := by
          intro equal; exact different (BitVec.eq_of_toNat_eq equal)
        have smaller : hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat < rank := by
          rw [hashProbeNext_wrap index capacity bits power inside,← distance]
          exact hashProbeDistance_decreases _ _ _ inside emptyInside naturalDifferent
        obtain ⟨finalResult,post,tail,cost,remaining,finalOutcome⟩ := ih _ smaller next (hashProbeNext index capacity)
          (nextValid continuing) nextInside rfl (by rw [ticks]; exact enough.2)
        rw [continuing] at run
        refine ⟨finalResult,post,run.trans tail,by omega,by omega,finalOutcome⟩
      · rw [returned] at run
        exact ⟨_,next,run,by omega,by omega,Or.inr ⟨index,inside,rfl⟩⟩

#print axioms evaluate_hashFindLoop_rank
end InitECandidate.Runtime
