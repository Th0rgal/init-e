import InitECandidate.Runtime.RlpLongTailDecCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The zero-word prefix of the actual `rlp_encode_word`: a single `0x80` byte at `dst`. -/
def rlpEncodeWordZero : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "w")) (.const (0#64)))
    (.seq (.storeByte (.var .local (ofString "dst")) (.const (128#64)))
      (.return (.const (1#64))))
    .skip

/-- The small-word prefix of the actual `rlp_encode_word`: the word itself as a single byte. -/
def rlpEncodeWordSmall : ProgHOL 64 :=
  .ite (.cmp .lower (.var .local (ofString "w")) (.const (128#64)))
    (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w")))
      (.return (.const (1#64))))
    .skip

/-- The long-word tail of the actual `rlp_encode_word`: the byte count of the word, its length byte
and then the word itself. -/
def rlpEncodeWordLong : ProgHOL 64 :=
  .decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
    (.seq (.storeByte (.var .local (ofString "dst"))
        (.op .add [.const (128#64), .var .local (ofString "ll")]))
      (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           .var .local (ofString "w"), .var .local (ofString "ll")])
        (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))

/-- The body equation of the actual `rlp_encode_word`. -/
theorem source_rlpEncodeWord_body :
    sourceFunctionBody Guest.guestFn_rlp_encode_word =
      .seq rlpEncodeWordZero (.seq rlpEncodeWordSmall rlpEncodeWordLong) := by
  rw [rlpEncodeWordZero,rlpEncodeWordSmall,rlpEncodeWordLong]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpEncodeWord_body

/-- A one-byte prefix: either the condition holds and a single byte is stored at `dst` followed by a
return, or it does not and the program continues unchanged.  Every word outside the nine-byte window
at `dst` keeps its cell. -/
theorem bytePrefix_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D w : BitVec 64) (cond : ExpHOL 64) (destination value : ExpHOL 64)
    (out : ¬ MWin D 9 w)
    (dstEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      destination = some (.val (.word D))) :
    (evaluateHOLFiniteState s (.ite cond
      (.seq (.storeByte destination value) (.return (.const (1#64)))) .skip)).2.memory w =
      s.memory w := by
  have sep : w ≠ panByteAlignHOL D := by
    intro h
    refine out ⟨0,by decide,Or.inr ?_⟩
    rw [show (D + BitVec.ofNat 64 0) = D from by simp]
    exact h
  have store := evaluate_storeByte_memory_frame s destination value D w dstEval sep
  have key : ∀ (r : Option (PanSemResultExact 64)) (st : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState s (.ite cond
        (.seq (.storeByte destination value) (.return (.const (1#64)))) .skip) = (r, st) →
      st.memory w = s.memory w := by
    intro r st run
    rw [evaluateHOLFiniteState_ite] at run
    split at run
    · rename_i word heq
      have hst : (if word = 0 then s.evaluateHOLFiniteState ProgHOL.skip
          else s.evaluateHOLFiniteState ((ProgHOL.storeByte destination value).seq
            (ProgHOL.return (ExpHOL.const (1#64))))).2 = st := by
        simpa using congrArg Prod.snd run
      rw [← hst]
      by_cases hz : word = 0
      · rw [if_pos hz,evaluateHOLFiniteState_skip]
      · rw [if_neg hz,evaluateHOLFiniteState_seq_line780]
        cases storeRun : evaluateHOLFiniteState s (.storeByte destination value) with
        | mk sr sPost =>
          rw [storeRun] at store
          dsimp only
          cases sr with
          | none => exact (return_memory sPost (.const (1#64)) w).trans store
          | some res => cases res <;> dsimp only <;> exact store
    · obtain ⟨_,hst⟩ := Prod.mk.inj run; rw [← hst]
  exact key _ _ rfl

#print axioms bytePrefix_window

/-- The store-and-return program always produces a result: the store either fails with an error or
continues to the return. -/
theorem storeReturn_some {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    ∃ r st, evaluateHOLFiniteState s
      (.seq (.storeByte destination value) (.return (.const (1#64)))) = (some r, st) := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases storeRun : evaluateHOLFiniteState s (.storeByte destination value) with
  | mk sr sPost =>
    dsimp only
    cases sr with
    | none =>
      rw [evaluateHOLFiniteState_return]
      dsimp only
      simp only [evalHOLExact]
      split <;> exact ⟨_,_,rfl⟩
    | some res => exact ⟨res,sPost,rfl⟩

#print axioms storeReturn_some

/-- A one-byte prefix continues only when its condition fails, and then the state is unchanged. -/
theorem bytePrefix_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (destination value : ExpHOL 64)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (.ite cond
      (.seq (.storeByte destination value) (.return (.const (1#64)))) .skip) = (none, mid)) :
    mid = s := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      injection run with _ h
      exact h.symm
    · obtain ⟨rr,ss,hss⟩ := storeReturn_some s destination value
      rw [if_neg hz,hss] at run
      simp at run
  · obtain ⟨_,hst⟩ := Prod.mk.inj run
    exact hst.symm

#print axioms bytePrefix_none

/-- The zero-word prefix writes at most the single byte at `dst`. -/
theorem rlpEncodeWordZero_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D w : BitVec 64) (out : ¬ MWin D 9 w)
    (dstEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "dst")) = some (.val (.word D))) :
    (evaluateHOLFiniteState s rlpEncodeWordZero).2.memory w = s.memory w :=
  bytePrefix_window s D w (.cmp .equal (.var .local (ofString "w")) (.const (0#64)))
    (.var .local (ofString "dst")) (.const (128#64)) out dstEval

#print axioms rlpEncodeWordZero_window

/-- The zero-word prefix continues unchanged. -/
theorem rlpEncodeWordZero_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s rlpEncodeWordZero = (none, mid)) : mid = s :=
  bytePrefix_none s (.cmp .equal (.var .local (ofString "w")) (.const (0#64)))
    (.var .local (ofString "dst")) (.const (128#64)) mid run

#print axioms rlpEncodeWordZero_none

/-- The small-word prefix writes at most the single byte at `dst`. -/
theorem rlpEncodeWordSmall_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D w : BitVec 64) (out : ¬ MWin D 9 w)
    (dstEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "dst")) = some (.val (.word D))) :
    (evaluateHOLFiniteState s rlpEncodeWordSmall).2.memory w = s.memory w :=
  bytePrefix_window s D w (.cmp .lower (.var .local (ofString "w")) (.const (128#64)))
    (.var .local (ofString "dst")) (.var .local (ofString "w")) out dstEval

#print axioms rlpEncodeWordSmall_window

/-- The small-word prefix continues unchanged. -/
theorem rlpEncodeWordSmall_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s rlpEncodeWordSmall = (none, mid)) : mid = s :=
  bytePrefix_none s (.cmp .lower (.var .local (ofString "w")) (.const (128#64)))
    (.var .local (ofString "dst")) (.var .local (ofString "w")) mid run

#print axioms rlpEncodeWordSmall_none

/-- **The actual `rlp_encode_word`.**  A zero word is `0x80`, a word below `0x80` is its own byte, and
a larger word is the length byte plus the real `rlp_be_len`/`rlp_put_be` big endian encoding.  Every
word outside the nine-byte window at `dst` keeps its cell. -/
theorem rlpEncodeWord_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D W w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hw : s.locals.lookup (ofString "w") = some (.val (.word W)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_word)).2.memory w =
      s.memory w := by
  have dstEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "dst")) = some (.val (.word D)) := by
    simp [evalHOLExact,hd]
  rw [source_rlpEncodeWord_body]
  rw [evaluateHOLFiniteState_seq_line780]
  cases zeroRun : evaluateHOLFiniteState s rlpEncodeWordZero with
  | mk r0 mid0 =>
    cases r0 with
    | some res =>
      have hz := rlpEncodeWordZero_window s D w out dstEval
      rw [zeroRun] at hz
      exact hz
    | none =>
      have zEq := rlpEncodeWordZero_none s mid0 zeroRun
      rw [zEq]
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      cases smallRun : evaluateHOLFiniteState s rlpEncodeWordSmall with
      | mk r1 mid1 =>
        cases r1 with
        | some res =>
          have hs := rlpEncodeWordSmall_window s D w out dstEval
          rw [smallRun] at hs
          exact hs
        | none =>
          have sEq := rlpEncodeWordSmall_none s mid1 smallRun
          rw [sEq]
          dsimp only
          rw [rlpEncodeWordLong]
          exact rlpLongTailDecCall_window s D W w out
            (.op .add [.const (128#64), .var .local (ofString "ll")])
            (ofString "w") (by decide) hd hw code

#print axioms rlpEncodeWord_window

end InitECandidate.Runtime
