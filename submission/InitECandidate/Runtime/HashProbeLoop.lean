import InitECandidate.Runtime.HashProbeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashProbeLoop : ProgHOL 64 :=
  .while (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))

/-- A stable, readable occupancy array and a known empty slot suffice to bound
    the actual source probe loop by distance to that slot. Reachability must
    separately establish those table invariants. -/
theorem evaluate_hashProbeLoop_bounded {F : Type}
    (capacity empty used : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat) :
    ∀ (rank : Nat) (state : PanSemStateFiniteExact 64 F) (index : BitVec 64),
    state.locals.lookup (ofString "i") = some (.val (.word index)) →
    state.locals.lookup (ofString "cap") = some (.val (.word capacity)) →
    state.locals.lookup (ofString "used") = some (.val (.word used)) →
    index.toNat < capacity.toNat →
    hashProbeDistance capacity.toNat index.toNat empty.toNat = rank → rank ≤ state.clock →
    (∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte) →
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + empty) = some 0 →
    ∃ post, evaluateHOLFiniteState state hashProbeLoop = (none,post) ∧
      state.clock ≤ post.clock + rank ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs := by
  classical
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state index indexLocal capacityLocal usedLocal inside distance budget readable emptyLoad
    obtain ⟨byte,loaded⟩ := readable index inside
    have condition := eval_hashProbeOccupied state (ofString "i") index used byte indexLocal usedLocal loaded
    let word := BitVec.ofNat 64 byte.toNat
    by_cases zero : word = 0
    · have run : evaluateHOLFiniteState state hashProbeLoop = (none,state) := by
        unfold hashProbeLoop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        have zeroLiteral : BitVec.ofNat 64 byte.toNat = (0#64) := zero
        simp [Compiler.Encoders.Asm.wordCmpHOL,zeroLiteral]
      exact ⟨state,run,by omega,by omega,rfl,rfl,rfl,rfl⟩
    · have notEmpty : index ≠ empty := by
        intro same
        rw [same,emptyLoad] at loaded
        have byteZero : byte = 0 := (Option.some.inj loaded).symm
        apply zero
        simp [word,byteZero]
      have different : index.toNat ≠ empty.toNat := by
        intro equal; exact notEmpty (BitVec.eq_of_toNat_eq equal)
      let next := hashProbeNext index capacity
      let nextState := setVarHOLFinite (ofString "i") (.val (.word next)) (decClockHOLFinite state)
      have nextInside : next.toNat < capacity.toNat := by
        rw [hashProbeNext_toNat index capacity bits power inside]
        apply Nat.mod_lt
        rw [power]; exact Nat.two_pow_pos bits
      have decreases : hashProbeDistance capacity.toNat next.toNat empty.toNat < rank := by
        rw [hashProbeNext_wrap index capacity bits power inside,← distance]
        exact hashProbeDistance_decreases _ _ _ inside emptyInside different
      have nextIndex : nextState.locals.lookup (ofString "i") = some (.val (.word next)) := by
        simp [nextState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have namesCap : ofString "i" ≠ ofString "cap" := by decide
      have namesUsed : ofString "i" ≠ ofString "used" := by decide
      have nextCap : nextState.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
        simp [nextState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesCap,capacityLocal,decClockHOLFinite]
      have nextUsed : nextState.locals.lookup (ofString "used") = some (.val (.word used)) := by
        simp [nextState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesUsed,usedLocal,decClockHOLFinite]
      obtain ⟨post,tail,cost,remaining,memory,globals,code,domain⟩ := ih _ decreases nextState next
        nextIndex nextCap nextUsed nextInside rfl
        (by change _ ≤ state.clock - 1; omega) readable emptyLoad
      have step := evaluate_hashProbeStep (decClockHOLFinite state) (ofString "i") index capacity indexLocal capacityLocal
      have run : evaluateHOLFiniteState state hashProbeLoop = evaluateHOLFiniteState nextState hashProbeLoop := by
        unfold hashProbeLoop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
        have zeroLiteral : BitVec.ofNat 64 byte.toNat ≠ (0#64) := zero
        have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 byte.toNat) 0 = true := by
          simp [Compiler.Encoders.Asm.wordCmpHOL,zeroLiteral]
        rw [if_pos flag]
        simp [show state.clock ≠ 0 by omega,step,fixClockHOLFinite]
        simp only [setVarHOLFinite,decClockHOLFinite,Nat.lt_irrefl,if_false,nextState,next]
      refine ⟨post,run.trans tail,?_,?_,memory,globals,code,domain⟩
      all_goals dsimp only [nextState,setVarHOLFinite,decClockHOLFinite] at cost remaining; omega

#print axioms evaluate_hashProbeLoop_bounded
end InitECandidate.Runtime
