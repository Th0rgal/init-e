import InitECandidate.Runtime.RlpPutBeStepLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The countdown loop of `rlp_put_be` writes only inside `[D, D+N)`: every byte it stores sits at
`dst + i` with `i < N`.  Hence any word outside that window, in particular every word below `dst`,
keeps its memory cell through the whole loop, whatever happens (normal exit, timeout, error).
This is the induction step, driven by an explicit bound on the countdown index. -/
theorem rlpPutBeLoop_window_aux {F : Type} (D N : BitVec 64) (w : BitVec 64)
    (out : ¬ MWin D N.toNat w) (n : Nat) :
    ∀ (s : PanSemStateFiniteExact 64 F) (I : BitVec 64),
      s.locals.lookup (ofString "dst") = some (.val (.word D)) →
      s.locals.lookup (ofString "i") = some (.val (.word I)) →
      I.toNat ≤ N.toNat → I.toNat ≤ n →
      (evaluateHOLFiniteState s rlpPutBeLoop).2.memory w = s.memory w := by
  induction n with
  | zero =>
    intro s I hd hi hIN hle
    have hI0 : I.toNat = 0 := by omega
    have hnot : ¬ ((0#64) < I) := by
      rw [BitVec.lt_def]
      simp [hI0]
    rw [rlpPutBeLoop,evaluateHOLFiniteState_while_total]
    dsimp only
    have condEval : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.const (0#64)) (.var .local (ofString "i"))) =
        some (.val (.word (0#64))) := by
      simp [evalHOLExact,hi,wordOp,valueWord,Compiler.Encoders.Asm.wordCmpHOL,hnot]
    rw [condEval]
    dsimp only
    rw [if_neg (by decide : ¬ ((0#64) ≠ 0))]
  | succ n ih =>
    intro s I hd hi hIN hle
    by_cases hzero : (0#64) < I
    · have hpos : 0 < I.toNat := by
        have := BitVec.lt_def.mp hzero
        simpa using this
      have condEval : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (.const (0#64)) (.var .local (ofString "i"))) =
          some (.val (.word (1#64))) := by
        simp [evalHOLExact,hi,wordOp,valueWord,Compiler.Encoders.Asm.wordCmpHOL,
          decide_eq_true hzero]
      rw [rlpPutBeLoop,evaluateHOLFiniteState_while_total]
      dsimp only
      rw [condEval]
      dsimp only
      rw [if_pos (by decide : (1#64) ≠ 0)]
      by_cases hclock : s.clock = 0
      · rw [if_pos hclock]
        rfl
      · rw [if_neg hclock]
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep with
        | mk rb bodyPost =>
        dsimp only
        have memStep : bodyPost.memory w = s.memory w := by
          have hm := rlpPutBeStep_memory (s := decClockHOLFinite s) D N w I hd hi out hpos hIN
          rw [bodyRun] at hm
          exact hm
        have hIN' : ((I - 1#64)).toNat ≤ N.toNat := by
          have h := rlpPutBe_sub_one hpos
          omega
        have hle' : ((I - 1#64)).toNat ≤ n := by
          have h := rlpPutBe_sub_one hpos
          omega
        have stepLocals := rlpPutBeStep_locals (s := decClockHOLFinite s) D I hd hi
        have hfixmem : (fixClockHOLFinite (decClockHOLFinite s)
            (evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep)).2.memory w =
            bodyPost.memory w := by
          rw [bodyRun]
          rfl
        have hd' : (fixClockHOLFinite (decClockHOLFinite s)
            (evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep)).2.locals.lookup
            (ofString "dst") = some (.val (.word D)) := by
          simpa only [fixClockHOLFinite] using stepLocals.2
        have hi' : (fixClockHOLFinite (decClockHOLFinite s)
            (evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep)).2.locals.lookup
            (ofString "i") = some (.val (.word (I - 1#64))) := by
          simpa only [fixClockHOLFinite] using stepLocals.1
        rcases rb with _ | (_ | _ | _ | _ | _ | _ | _)
        · -- normal completion: the loop goes on from the fixed post state
          dsimp only
          rw [← bodyRun]
          exact (ih (fixClockHOLFinite (decClockHOLFinite s)
            (evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep)).2 (I - 1#64)
            hd' hi' hIN' hle').trans (hfixmem.trans memStep)
        · dsimp only
          exact memStep
        · dsimp only
          exact memStep
        · dsimp only
          exact memStep
        · -- explicit `continue`: the loop also goes on
          dsimp only
          rw [← bodyRun]
          exact (ih (fixClockHOLFinite (decClockHOLFinite s)
            (evaluateHOLFiniteState (decClockHOLFinite s) rlpPutBeStep)).2 (I - 1#64)
            hd' hi' hIN' hle').trans (hfixmem.trans memStep)
        · dsimp only
          exact memStep
        · dsimp only
          exact memStep
        · dsimp only
          exact memStep
    · have condEval : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (.const (0#64)) (.var .local (ofString "i"))) =
          some (.val (.word (0#64))) := by
        simp [evalHOLExact,hi,wordOp,valueWord,Compiler.Encoders.Asm.wordCmpHOL,hzero]
      rw [rlpPutBeLoop,evaluateHOLFiniteState_while_total]
      dsimp only
      rw [condEval]
      dsimp only
      rw [if_neg (by decide : ¬ ((0#64) ≠ 0))]

#print axioms rlpPutBeLoop_window_aux

/-- The countdown loop of `rlp_put_be` writes only inside `[D, D+N)`: every byte it stores sits at
`dst + i` with `i < N`.  Hence any word outside that window, in particular every word below `dst`,
keeps its memory cell through the whole loop, whatever happens (normal exit, timeout, error). -/
theorem rlpPutBeLoop_window {F : Type} (D N : BitVec 64) (w : BitVec 64) (out : ¬ MWin D N.toNat w)
    (s : PanSemStateFiniteExact 64 F) (I : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (hIN : I.toNat ≤ N.toNat) :
    (evaluateHOLFiniteState s rlpPutBeLoop).2.memory w = s.memory w :=
  rlpPutBeLoop_window_aux D N w out I.toNat s I hd hi hIN (le_refl _)

#print axioms rlpPutBeLoop_window

end InitECandidate.Runtime
