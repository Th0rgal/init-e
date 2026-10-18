import InitECandidate.Runtime.DecodeRequestsBodyBound
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.SszLe32Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Offset loop invariant that also tracks that only scratch cells ssz_offs+8k (k < i) changed. -/
def ReqLoopInvF {σ : Type} (base : PanSemStateFiniteExact 64 σ) (offsets : BitVec 64) (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i : BitVec 64, ∃ L M, s = {base with locals := L, memory := M, clock := s.clock} ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ 5 ∧
    (∀ k, k ≠ ofString "i" → L.lookup k = base.locals.lookup k) ∧
    ∀ a, (∀ k : BitVec 64, k.toNat < i.toNat → a ≠ offsets + k * 8) → M a = base.memory a

theorem evaluate_reqLoop_frame {σ : Type} (base s : PanSemStateFiniteExact 64 σ) (offsets : BitVec 64)
    (hg : base.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (inv : ReqLoopInvF base offsets s) (ticks : reqLoopRank s ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s reqLoop = (result, post) ∧
      (result = none → ReqLoopInvF base offsets post ∧ reqLoopRank post = 0) := by
  have rankEq : ∀ (t : PanSemStateFiniteExact 64 σ) (i : BitVec 64),
      t.locals.lookup (ofString "i") = some (.val (.word i)) → reqLoopRank t = 5 - i.toNat := by
    intro t i h; simp [reqLoopRank, h]
  have guard : ∀ state, ReqLoopInvF base offsets state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (sszLocal "i") (.const 5)) =
        some (.val (.word (if reqLoopRank state = 0 then 0 else 1))) := by
    rintro state ⟨i, L, M, shape, hi, le, _⟩
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    rw [rankEq state i si]
    by_cases zero : 5 - i.toNat = 0
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      omega
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      omega
  have entry : ∀ state, ReqLoopInvF base offsets state → ReqLoopInvF base offsets (decClockHOLFinite state) := by
    rintro state ⟨i, L, M, shape, rest⟩
    exact ⟨i, L, M, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, reqLoopRank (decClockHOLFinite state) = reqLoopRank state := by
    intro state; rfl
  have step : ∀ state, ReqLoopInvF base offsets state → 0 < reqLoopRank state → 0 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 0 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state reqLoopBody = (none,post) ∧ ReqLoopInvF base offsets post ∧
            reqLoopRank post < reqLoopRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state reqLoopBody = (some result,post))) := by
    rintro state ⟨i, L, M, shape, hi, le, others, frame⟩ positive _
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    have sg : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [shape]; exact hg
    rw [rankEq state i si] at positive
    have addr : @evalHOLExact 64 σ _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.op .add [reqGlobal, .panop .mul [sszLocal "i", .const 8]]) = some (.val (.word (offsets + i * 8))) := by
      simp [reqGlobal, sszLocal, evalHOLExact, evalListHOLExact, si, sg, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL]
    have wordValue := @sszSplitOffsetAt_bounded σ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
    have memFrame := fun (a : BitVec 64) (ne : a ≠ offsets + i * 8) =>
      evaluate_wordStore_memory_frame state _ sszSplitOffsetAt (offsets + i * 8) a addr
        (fun v h => by obtain ⟨w, hw, _⟩ := wordValue v h; exact ⟨w, hw⟩) ne
    unfold reqLoopBody
    rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluate_store_cases state (.op .add [reqGlobal, .panop .mul [sszLocal "i", .const 8]]) sszSplitOffsetAt
      with err | ⟨M', ok⟩
    · rw [err]
      exact ⟨state, by omega, Nat.le_refl _, Or.inr ⟨.error, by simp, by simp, by simp, by simp, rfl⟩⟩
    · rw [ok] at memFrame ⊢
      dsimp only at memFrame ⊢
      rw [sszSplit_assign_i ({state with memory := M'} : PanSemStateFiniteExact 64 σ) i si]
      have succ : (i + 1).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      refine ⟨_, by simp [setVarHOLFinite], by simp [setVarHOLFinite], Or.inl ⟨rfl, ?_, ?_⟩⟩
      · refine ⟨i + 1, (setVarHOLFinite (ofString "i") (.val (.word (i + 1)))
          ({state with memory := M'} : PanSemStateFiniteExact 64 σ)).locals, M', ?_,
          by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], by omega, ?_, ?_⟩
        · rw [shape]; rfl
        · intro k hk
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          rw [shape]; exact others k hk
        · intro a ex
          rw [succ] at ex
          have stateMem : state.memory = M := by rw [shape]
          rw [memFrame a (ex i (by omega)), stateMem]
          exact frame a (fun k hk => ex k (by omega))
      · rw [rankEq _ (i + 1) (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]), rankEq state i si,
          succ]
        omega
  obtain ⟨result, post, run, _, _, _, normal, _⟩ := evaluate_ranked_loop_exits_invariant _ reqLoopBody
    (ReqLoopInvF base offsets) reqLoopRank 0 guard entry entryRank step s inv (by simpa using ticks)
  exact ⟨result, post, by simpa [reqLoop] using run, normal⟩

#print axioms evaluate_reqLoop_frame
end InitECandidate.Runtime
