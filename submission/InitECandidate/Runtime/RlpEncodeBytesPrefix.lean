import InitECandidate.Runtime.RlpWriteHeaderReturns
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The single-byte prefix of the actual `rlp_encode_bytes`: when the length is one and the byte is
below `0x80`, that byte is stored at `dst` and the writer returns. -/
def rlpEncodeBytesPrefix : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "n")) (.const (1#64)))
    (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const (128#64)))
        (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
          (.return (.const (1#64))))
        .skip))
    .skip

/-- The header-and-copy tail of the actual `rlp_encode_bytes`: the real `rlp_write_header` writes
the string header at `dst`, the real `memcpy` copies `n` bytes to `dst + h`, and the writer returns
`h + n`. -/
def rlpEncodeBytesTail : ProgHOL 64 :=
  .decCall (ofString "h") .one (ofString "rlp_write_header")
    [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")]
    (.seq (.call (some (none,none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
         .var .local (ofString "src"), .var .local (ofString "n")])
      (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))

/-- The body equation of the actual `rlp_encode_bytes`. -/
theorem source_rlpEncodeBytes_body :
    sourceFunctionBody Guest.guestFn_rlp_encode_bytes =
      .seq rlpEncodeBytesPrefix rlpEncodeBytesTail := by
  rw [rlpEncodeBytesPrefix,rlpEncodeBytesTail]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpEncodeBytes_body

/-- A `dec` whose body keeps the watched cell keeps it too: initializer failure and a failed shape
check both return the unchanged state, and the body runs from the state with the bound local, which
does not touch memory. -/
theorem dec_window {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL 64) (body : ProgHOL 64) (w : BitVec 64)
    (hbody : ∀ (v : ValueHOL 64),
      (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.dec name shape initializer body)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hinit : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) initializer with
  | none => rfl
  | some value =>
    dsimp only
    by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
    · rw [if_pos hshape]
      dsimp only
      exact hbody value
    · rw [if_neg hshape]

#print axioms dec_window

/-- The single-byte prefix writes only inside the nine-byte window at `dst`. -/
theorem rlpEncodeBytesPrefix_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D))) :
    (evaluateHOLFiniteState s rlpEncodeBytesPrefix).2.memory w = s.memory w := by
  rw [rlpEncodeBytesPrefix,evaluateHOLFiniteState_ite]
  split
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip]
    · rw [if_neg hz]
      refine dec_window s (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        _ w ?_
      intro v
      have dstEval : @evalHOLExact 64 F _
          (setVarHOLFinite (ofString "b") v s).toExact
          (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "b") v s).memaddrs a))
          (.var .local (ofString "dst")) = some (.val (.word D)) := by
        simp [evalHOLExact,lookup_setVar_ne s (ofString "b") (ofString "dst") v _ (by decide) hd]
      exact bytePrefix_window (setVarHOLFinite (ofString "b") v s) D w
        (.cmp .lower (.var .local (ofString "b")) (.const (128#64)))
        (.var .local (ofString "dst")) (.var .local (ofString "b")) out dstEval
  · rfl

#print axioms rlpEncodeBytesPrefix_window

/-- Reading a restored local that was not the bound one. -/
theorem lookup_resVarEq_ne (map : HolFiniteMapExact MlS (ValueHOL 64)) (key name : MlS)
    (e : Option (ValueHOL 64)) (h : name ≠ key) :
    (HolFiniteMapExact.resVarEq map (key,e)).lookup name = map.lookup name := by
  cases e with
  | none => simp only [HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL,h,
      Bool.false_eq_true,if_false]
  | some v => simp only [HolFiniteMapExact.lookup_resVarEq_some,FUPDATE_HOL,h,
      Bool.false_eq_true,if_false]

#print axioms lookup_resVarEq_ne

/-- A local assignment leaves an unbound other variable unbound. -/
theorem lookup_setVar_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (name other : MlS)
    (v : ValueHOL 64) (ne : name ≠ other) (hx : s.locals.lookup other = none) :
    (setVarHOLFinite name v s).locals.lookup other = none := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne,hx]

#print axioms lookup_setVar_ne_none

/-- A continuing single-byte prefix leaves memory, code and globals untouched and keeps every local
other than the bound `b` readable as before. -/
theorem rlpEncodeBytesPrefix_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s rlpEncodeBytesPrefix = (none, mid)) :
    mid.memory = s.memory ∧ mid.code = s.code ∧ mid.globals = s.globals ∧
      ∀ (name : MlS), name ≠ ofString "b" → mid.locals.lookup name = s.locals.lookup name := by
  rw [rlpEncodeBytesPrefix,evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      obtain ⟨_,hmid⟩ := Prod.mk.inj run
      rw [← hmid]
      exact ⟨rfl,rfl,rfl,fun name _ => rfl⟩
    · rw [if_neg hz] at run
      rw [evaluateHOLFiniteState_dec_total] at run
      dsimp only at run
      split at run
      · simp at run
      · rename_i value hinit
        split at run
        · rename_i hshape
          cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "b") value s)
              (.ite (.cmp .lower (.var .local (ofString "b")) (.const (128#64)))
                (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
                  (.return (.const (1#64)))) .skip) with
          | mk br bst =>
            rw [bodyRun] at run
            dsimp only at run
            obtain ⟨hbr,hmid⟩ := Prod.mk.inj run
            rw [hbr] at bodyRun
            have bstEq : bst = setVarHOLFinite (ofString "b") value s :=
              bytePrefix_none (setVarHOLFinite (ofString "b") value s)
                (.cmp .lower (.var .local (ofString "b")) (.const (128#64)))
                (.var .local (ofString "dst")) (.var .local (ofString "b")) bst bodyRun
            rw [← hmid,bstEq]
            refine ⟨by simp [setVarHOLFinite],by simp [setVarHOLFinite],
              by simp [setVarHOLFinite],?_⟩
            intro name hname
            have hk : (setVarHOLFinite (ofString "b") value s).locals.lookup name
                = s.locals.lookup name := by
              cases hx : s.locals.lookup name with
              | none =>
                exact lookup_setVar_ne_none s (ofString "b") name value
                  (fun h => hname h.symm) hx
              | some x =>
                exact lookup_setVar_ne s (ofString "b") name value x
                  (fun h => hname h.symm) hx
            rw [lookup_resVarEq_ne _ (ofString "b") name _ hname]
            exact hk
        · simp at run
  · simp at run

#print axioms rlpEncodeBytesPrefix_none

end InitECandidate.Runtime
