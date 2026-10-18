import InitECandidate.Runtime.StoreAdvanceStep
import InitECandidate.Runtime.MemcpyByte1LoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def storeTail1Rank {F : Type} (size : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => (size.toNat - index.toNat)
  | _ => 0

/-- Any store-and-advance-by-one loop guarded by i < n consumes at most one clock per remaining byte. -/
theorem evaluate_storeAdvance_tail1_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64) (body : ProgHOL 64)
    (supported : StoreAdvanceStep (ofString "i") 1 body)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) body) = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ finalIndex = size) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word size)) ∧ i.toNat ≤ size.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      storeTail1Rank size current = (size.toNat - i.toNat) := by
    intro current i binding; simp [storeTail1Rank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if storeTail1Rank size current = 0 then 0 else 1))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩
    by_cases enabled : i.toNat < size.toNat
    · have nonzero : size.toNat - i.toNat ≠ 0 := by omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atSize,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i atIndex,nonzero]
    · have zero : size.toNat - i.toNat = 0 := by omega
      simp [evalHOLFinite,evalHOLExact,atIndex,atSize,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i atIndex,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩; exact ⟨i,atIndex,atSize,bounded⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      storeTail1Rank size (decClockHOLFinite current) = storeTail1Rank size current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < storeTail1Rank size current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current body = (none,post) ∧ invariant post ∧
          storeTail1Rank size post < storeTail1Rank size current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current body = (some result,post))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_storeAdvanceStep supported current i atIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl
    · have natural : (i + 1).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)]; rfl
      rw [rankEq current i atIndex] at positive
      refine Or.inl ⟨run,⟨i+1,advanced,(locals _ (by decide)).trans atSize,by omega⟩,?_⟩
      rw [rankEq post (i+1) advanced,rankEq current i atIndex,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro value; simp),run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) body invariant (storeTail1Rank size) 0 guard enter entryRank step state
    ⟨index,indexLocal,sizeLocal,inside⟩ (by simpa [rankEq state index indexLocal] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · exact run
  · simpa [rankEq state index indexLocal] using cost
  · intro normal
    obtain ⟨⟨i,atIndex,atSize,bounded⟩,zero⟩ := done normal
    rw [rankEq post i atIndex] at zero
    have equal : i = size := BitVec.eq_of_toNat_eq (by omega)
    exact ⟨i,atIndex,atSize,bounded,equal⟩

#print axioms evaluate_storeAdvance_tail1_loop_bounded
end InitECandidate.Runtime
