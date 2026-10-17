import InitECandidate.Runtime.MemcpyByte1LoopBound
import InitECandidate.Runtime.MemcpyByte1MemoryFrame
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real unaligned copy loop consumes at most one clock per eight-byte
block, including arbitrary load/store failures. -/
theorem evaluate_memcpy_byte1_loop_memory_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (separate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memcpyByte1Loop = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ finalIndex = size ∧
        post.locals.lookup (ofString "dst") = some (.val (.word destination)) ∧
        post.locals.lookup (ofString "src") = some (.val (.word source)) ∧
        post.memory watched = state.memory watched) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word size)) ∧ i.toNat ≤ size.toNat ∧
    current.locals.lookup (ofString "dst") = some (.val (.word destination)) ∧
    current.locals.lookup (ofString "src") = some (.val (.word source)) ∧ current.memory watched = state.memory watched
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      memcpyByte1Rank size current = (size.toNat - i.toNat) := by
    intro current i binding; simp [memcpyByte1Rank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if memcpyByte1Rank size current = 0 then 0 else 1))) := by
    rintro current ⟨i,atIndex,atSize,bounded,atDst,atSrc,saved⟩
    by_cases enabled : i.toNat < size.toNat
    · have nonzero : size.toNat - i.toNat ≠ 0 := by omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atSize,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i atIndex,nonzero]
    · have zero : size.toNat - i.toNat = 0 := by omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atSize,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i atIndex,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,atIndex,atSize,bounded,atDst,atSrc,saved⟩; exact ⟨i,atIndex,atSize,bounded,atDst,atSrc,saved⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      memcpyByte1Rank size (decClockHOLFinite current) = memcpyByte1Rank size current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < memcpyByte1Rank size current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memcpyByte1Body = (none,post) ∧ invariant post ∧
          memcpyByte1Rank size post < memcpyByte1Rank size current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current memcpyByte1Body = (some result,post))) := by
    rintro current ⟨i,atIndex,atSize,bounded,atDst,atSrc,saved⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_byteAdvanceStep (show ByteAdvanceStep (ofString "i") 1 memcpyByte1Body from ByteAdvanceStep.store _ _ ByteAdvanceStep.advance) current i atIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl
    · have natural : (i + 1).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)]; rfl
      rw [rankEq current i atIndex] at positive
      have frame := evaluate_memcpy_byte1_memory_frame current destination i watched atDst atIndex (by
        simpa using separate i.toNat (by omega))
      rw [run] at frame
      refine Or.inl ⟨run,⟨i+1,advanced,(locals _ (by decide)).trans atSize,by omega,
        (locals _ (by decide)).trans atDst,(locals _ (by decide)).trans atSrc,frame.trans saved⟩,?_⟩
      rw [rankEq post (i+1) advanced,rankEq current i atIndex,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro value; simp),run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    ((.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))) memcpyByte1Body invariant (memcpyByte1Rank size) 0 guard enter entryRank step state
    ⟨index,indexLocal,sizeLocal,inside,dstLocal,srcLocal,rfl⟩ (by simpa [rankEq state index indexLocal] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_memcpy_byte1_loop]; exact run
  · simpa [rankEq state index indexLocal] using cost
  · intro normal
    obtain ⟨⟨i,atIndex,atSize,bounded,atDst,atSrc,saved⟩,zero⟩ := done normal
    rw [rankEq post i atIndex] at zero
    exact ⟨i,atIndex,atSize,bounded,BitVec.eq_of_toNat_eq (by omega),atDst,atSrc,saved⟩

#print axioms evaluate_memcpy_byte1_loop_memory_bounded
end InitECandidate.Runtime
