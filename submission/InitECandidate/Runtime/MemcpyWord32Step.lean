import InitECandidate.Runtime.MemcpyWordOffset
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyWord32Body : ProgHOL 64 :=
  .seq (memcpyWordStore 0) (.seq (memcpyWordStore 8)
    (.seq (memcpyWordStore 16) (.seq (memcpyWordStore 24) (memzeroAdvance 32))))

theorem source_memcpy_word32_loop : memcpyWord32Loop =
    .while (memzeroBlockCondition 32) memcpyWord32Body := by rfl

/-- All four stores of the original32-byte copy block execute in source order
before advancing i; contents and source/destination overlap are unrestricted. -/
theorem evaluate_memcpy_word32_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)), state.memaddrs (destination + index + offset))
    (sourceDomain : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)), state.memaddrs (source + index + offset)) :
    ∃ post, evaluateHOLFiniteState state memcpyWord32Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 32))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ∀ capacity used : BitVec 64,
        (∀ offset ∈ ([0,8,16,24] : List (BitVec 64)), ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
          panByteAlignHOL (used + slot) ≠ destination + index + offset) →
        hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) := by
  obtain ⟨s1,run1,ticks1,local1,global1,code1,domain1,endian1,counts1⟩ :=
    evaluate_memcpy_word_store state destination source index 0 dstLocal srcLocal indexLocal
      (destinationDomain 0 (by simp)) (sourceDomain 0 (by simp))
  have locals1 : s1.locals = state.locals := local1
  have clock1 : s1.clock = state.clock := ticks1
  have globals1 : s1.globals = state.globals := global1
  have codes1 : s1.code = state.code := code1
  have addresses1 : s1.memaddrs = state.memaddrs := domain1
  have endians1 : s1.be = state.be := endian1
  obtain ⟨s2,run2,ticks2,local2,global2,code2,domain2,endian2,counts2⟩ :=
    evaluate_memcpy_word_store s1 destination source index 8 (by rw [locals1]; exact dstLocal) (by rw [locals1]; exact srcLocal) (by rw [locals1]; exact indexLocal)
      (by rw [addresses1]; exact destinationDomain 8 (by simp)) (by rw [addresses1]; exact sourceDomain 8 (by simp))
  have locals2 : s2.locals = state.locals := local2.trans locals1
  have clock2 : s2.clock = state.clock := ticks2.trans clock1
  have globals2 : s2.globals = state.globals := global2.trans globals1
  have codes2 : s2.code = state.code := code2.trans codes1
  have addresses2 : s2.memaddrs = state.memaddrs := domain2.trans addresses1
  have endians2 : s2.be = state.be := endian2.trans endians1
  obtain ⟨s3,run3,ticks3,local3,global3,code3,domain3,endian3,counts3⟩ :=
    evaluate_memcpy_word_store s2 destination source index 16 (by rw [locals2]; exact dstLocal) (by rw [locals2]; exact srcLocal) (by rw [locals2]; exact indexLocal)
      (by rw [addresses2]; exact destinationDomain 16 (by simp)) (by rw [addresses2]; exact sourceDomain 16 (by simp))
  have locals3 : s3.locals = state.locals := local3.trans locals2
  have clock3 : s3.clock = state.clock := ticks3.trans clock2
  have globals3 : s3.globals = state.globals := global3.trans globals2
  have codes3 : s3.code = state.code := code3.trans codes2
  have addresses3 : s3.memaddrs = state.memaddrs := domain3.trans addresses2
  have endians3 : s3.be = state.be := endian3.trans endians2
  obtain ⟨s4,run4,ticks4,local4,global4,code4,domain4,endian4,counts4⟩ :=
    evaluate_memcpy_word_store s3 destination source index 24 (by rw [locals3]; exact dstLocal) (by rw [locals3]; exact srcLocal) (by rw [locals3]; exact indexLocal)
      (by rw [addresses3]; exact destinationDomain 24 (by simp)) (by rw [addresses3]; exact sourceDomain 24 (by simp))
  have locals4 : s4.locals = state.locals := local4.trans locals3
  have clock4 : s4.clock = state.clock := ticks4.trans clock3
  have globals4 : s4.globals = state.globals := global4.trans globals3
  have codes4 : s4.code = state.code := code4.trans codes3
  have addresses4 : s4.memaddrs = state.memaddrs := domain4.trans addresses3
  have endians4 : s4.be = state.be := endian4.trans endians3
  have advance := evaluate_memzero_advance s4 index 32 (by rw [locals4]; exact indexLocal)
  have run : evaluateHOLFiniteState state memcpyWord32Body =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 32))) s4) := by
    unfold memcpyWord32Body
    rw [evaluateHOLFiniteState_seq_line780,run1]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,run2]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,run3]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,run4]
    exact advance
  refine ⟨_,run,clock4,?_,globals4,codes4,addresses4,endians4,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals4]
  · intro capacity used separate
    change hashOccupiedCount capacity (hashOccupancyRead s4 used) = _
    rw [counts4 capacity used (separate 24 (by simp)),counts3 capacity used (separate 16 (by simp)),
      counts2 capacity used (separate 8 (by simp)),counts1 capacity used (separate 0 (by simp))]

#print axioms source_memcpy_word32_loop
#print axioms evaluate_memcpy_word32_step
end InitECandidate.Runtime
