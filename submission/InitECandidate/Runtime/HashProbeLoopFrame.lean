import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A stable, readable occupancy array and a known empty slot suffice to bound
    the actual source probe loop by distance to that slot. Reachability must
    separately establish those table invariants. -/
theorem evaluate_hashProbeLoop_bounded_frame {F : Type}
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
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∃ finalIndex : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        finalIndex.toNat < capacity.toNat ∧
        @panMemLoadByteHOL 64 _ state.memory state.memaddrs
          (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + finalIndex) = some 0 ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
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
      have byteZero : byte = 0 := by
        apply UInt8.toNat.inj
        have limit := byte.toNat_lt_size
        change byte.toNat < 256 at limit
        have equality := congrArg BitVec.toNat zero
        simpa [word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show byte.toNat < 2^64 by omega)] using equality
      refine ⟨state,run,by omega,by omega,rfl,rfl,rfl,rfl,rfl,index,indexLocal,inside,?_,?_⟩
      · simpa only [byteZero] using loaded
      · intro name different; rfl
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
      obtain ⟨post,tail,cost,remaining,memory,globals,code,domain,endian,finalIndex,finalLocal,finalInside,finalEmpty,otherLocals⟩ := ih _ decreases nextState next
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
      refine ⟨post,run.trans tail,?_,?_,memory,globals,code,domain,endian,finalIndex,finalLocal,finalInside,finalEmpty,?_⟩
      · dsimp only [nextState,setVarHOLFinite,decClockHOLFinite] at cost remaining
        omega
      · dsimp only [nextState,setVarHOLFinite,decClockHOLFinite] at remaining
        omega
      · intro name different
        rw [otherLocals name different]
        have backwards := Ne.symm different
        simp [nextState,setVarHOLFinite,decClockHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,backwards]

theorem evaluate_hashProbeLoop_capacity_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used index : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (inside : index.toNat < capacity.toNat) (clock : capacity.toNat ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashProbeLoop = (none,post) ∧
      state.clock < post.clock + capacity.toNat ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∃ finalIndex : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        finalIndex.toNat < capacity.toNat ∧ hashOccupancyRead state used finalIndex = some 0 ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) room
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat inside emptyInside
  obtain ⟨post,run,cost,remaining,memory,globals,code,domain,endian,final⟩ :=
    evaluate_hashProbeLoop_bounded_frame capacity empty used bits power emptyInside _ state index
      indexLocal capacityLocal usedLocal inside rfl (by omega) readable emptyLoad
  exact ⟨post,run,by omega,remaining,memory,globals,code,domain,endian,final⟩

#print axioms evaluate_hashProbeLoop_bounded_frame
#print axioms evaluate_hashProbeLoop_capacity_frame
end InitECandidate.Runtime
