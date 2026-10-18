import InitECandidate.Runtime.DecodeRequestsAllocCheck
import InitECandidate.Runtime.RankedLoopExitsInvariant
import InitECandidate.Runtime.SszSplitVarListStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_store_cases {σ : Type} (s : PanSemStateFiniteExact 64 σ) (d v : ExpHOL 64) :
    evaluateHOLFiniteState s (.store d v) = (some .error, s) ∨
      ∃ M, evaluateHOLFiniteState s (.store d v) = (none, {s with memory := M}) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

def ReqLoopInv {σ : Type} (base s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i : BitVec 64, ∃ L M, s = {base with locals := L, memory := M, clock := s.clock} ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ 5 ∧
    ∀ k, k ≠ ofString "i" → L.lookup k = base.locals.lookup k

def reqLoopRank {σ : Type} (s : PanSemStateFiniteExact 64 σ) : Nat :=
  match s.locals.lookup (ofString "i") with
  | some (.val (.word i)) => 5 - i.toNat
  | _ => 0

theorem evaluate_reqLoop {σ : Type} (base s : PanSemStateFiniteExact 64 σ) (inv : ReqLoopInv base s)
    (ticks : reqLoopRank s ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s reqLoop = (result, post) ∧
      s.clock ≤ post.clock + reqLoopRank s * 1 ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → ReqLoopInv base post ∧ reqLoopRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have rankEq : ∀ (t : PanSemStateFiniteExact 64 σ) (i : BitVec 64),
      t.locals.lookup (ofString "i") = some (.val (.word i)) → reqLoopRank t = 5 - i.toNat := by
    intro t i h; simp [reqLoopRank, h]
  have guard : ∀ state, ReqLoopInv base state →
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
  have entry : ∀ state, ReqLoopInv base state → ReqLoopInv base (decClockHOLFinite state) := by
    rintro state ⟨i, L, M, shape, rest⟩
    exact ⟨i, L, M, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, reqLoopRank (decClockHOLFinite state) = reqLoopRank state := by
    intro state; rfl
  have step : ∀ state, ReqLoopInv base state → 0 < reqLoopRank state → 0 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 0 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state reqLoopBody = (none,post) ∧ ReqLoopInv base post ∧
            reqLoopRank post < reqLoopRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state reqLoopBody = (some result,post))) := by
    rintro state ⟨i, L, M, shape, hi, le, others⟩ positive _
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    rw [rankEq state i si] at positive
    unfold reqLoopBody
    rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluate_store_cases state (.op .add [reqGlobal, .panop .mul [sszLocal "i", .const 8]]) sszSplitOffsetAt
      with err | ⟨M', ok⟩
    · rw [err]
      exact ⟨state, by omega, Nat.le_refl _, Or.inr ⟨.error, by simp, by simp, by simp, by simp, rfl⟩⟩
    · rw [ok]
      dsimp only
      rw [sszSplit_assign_i ({state with memory := M'} : PanSemStateFiniteExact 64 σ) i si]
      refine ⟨_, by simp [setVarHOLFinite], by simp [setVarHOLFinite], Or.inl ⟨rfl, ?_, ?_⟩⟩
      · refine ⟨i + 1, (setVarHOLFinite (ofString "i") (.val (.word (i + 1))) ({state with memory := M'} : PanSemStateFiniteExact 64 σ)).locals, M', ?_,
          by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_, ?_⟩
        · rw [shape]; rfl
        · rw [BitVec.toNat_add]; simp; omega
        · intro k hk
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          rw [shape]; exact others k hk
      · rw [rankEq _ (i + 1) (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]), rankEq state i si]
        rw [BitVec.toNat_add]; simp; omega
  have result := evaluate_ranked_loop_exits_invariant _ reqLoopBody (ReqLoopInv base) reqLoopRank 0
    guard entry entryRank step s inv (by simpa using ticks)
  simpa [reqLoop] using result

#print axioms evaluate_reqLoop

theorem reqAfterLen_bounded {σ : Type} (e : PanSemStateFiniteExact 64 σ) (L pointer offsets : BitVec 64)
    (installed : e.code = originalRuntimeCode)
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (hg : e.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) (enough : 354 ≤ e.clock) :
    e.clock ≤ (evaluateHOLFiniteState e reqAfterLen).2.clock + 354 ∧
      (evaluateHOLFiniteState e reqAfterLen).2.clock ≤ e.clock ∧
      (evaluateHOLFiniteState e reqAfterLen).1 ≠ some .timeOut := by
  unfold reqAfterLen
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  generalize hq : setVarHOLFinite (ofString "i") (.val (.word 0#64)) e = q
  have qi : q.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have qc : q.clock = e.clock := by rw [← hq]; rfl
  have inv : ReqLoopInv q q := ⟨0#64, q.locals, q.memory, rfl, qi, by simp, fun _ _ => rfl⟩
  have rank : reqLoopRank q = 5 := by simp [reqLoopRank, qi]
  obtain ⟨result, post, run, l1, l2, nt, normal, _⟩ := evaluate_reqLoop q q inv (by omega)
  rw [rank] at l1
  rw [evaluateHOLFiniteState_seq_line780, run]
  cases result with
  | none =>
    obtain ⟨⟨i, Lp, M, shape, _, _, others⟩, _⟩ := normal rfl
    have li : ofString "len" ≠ ofString "i" := by decide_cbv
    have pre : ReqCheckPre post := by
      refine ⟨⟨by rw [shape, ← hq]; exact installed, ⟨L, ?_⟩, pointer, by rw [shape, ← hq]; exact heap, pointerBound⟩,
        offsets, by rw [shape, ← hq]; exact hg⟩
      rw [shape]; dsimp only
      rw [others _ li, ← hq]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm li, hlen]
    obtain ⟨a1, a2, a3⟩ := reqCheckAlloc_bounded post pre (by omega)
    dsimp only
    exact ⟨by omega, by omega, a3⟩
  | some x =>
    dsimp only
    exact ⟨by omega, by omega, nt⟩

/-- The actual decode_requests body costs at most 354 source ticks at every
clock, and does not time out when that much clock is available. -/
theorem evaluate_decodeRequests_body_bounded {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (L pointer offsets : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (hg : e.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)
    e.clock ≤ out.2.clock + 354 ∧ out.2.clock ≤ e.clock ∧ (354 ≤ e.clock → out.1 ≠ some .timeOut) := by
  intro out
  have lower := evaluateHOLFiniteState_clock_le e (sourceFunctionBody Guest.guestFn_decode_requests)
  by_cases enough : 354 ≤ e.clock
  · refine ⟨?_, lower, fun _ => ?_⟩ <;> (
    show _
    simp only [out]
    rw [source_decodeRequests_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    by_cases short : L < 20
    · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 20)) = some (.val (.word 1#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact short
      rw [cond]
      dsimp only
      rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
      obtain ⟨x, run, abnormal, c1, _⟩ := sszFail_abnormal e 60 installed (by omega)
      rw [run]
      dsimp only
      first | omega | exact fun h => abnormal.2.1 (Option.some.inj (run.symm.trans h))
    · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 20)) = some (.val (.word 0#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact BitVec.not_lt.mp short
      rw [cond]
      dsimp only
      rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
      dsimp only
      have r := reqAfterLen_bounded e L pointer offsets installed hlen heap pointerBound hg enough
      first | exact r.1 | exact r.2.2)
  · exact ⟨by omega, lower, fun h => absurd h enough⟩

#print axioms evaluate_decodeRequests_body_bounded
end InitECandidate.Runtime
