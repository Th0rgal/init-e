import InitECandidate.Runtime.RlpWriteHeaderContWindow
import InitECandidate.Runtime.RlpCalleeValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A one-word shape pins a value to a word. -/
theorem shapeWord_of_one {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with
    | word y => exact ⟨y,rfl⟩
  | _ => simp [shapeOfHOLExact,shapeEqHOL] at h

#print axioms shapeWord_of_one

/-- **The actual long-header tail of `rlp_write_header`.**  It reads the byte count from the real
`rlp_be_len` call (which writes no memory and returns a word of at most eight bytes), stores the
length byte at `dst`, writes the count at `dst + 1` through the real `rlp_put_be`, and returns the
total length.  Every word outside the nine-byte window at `dst` keeps its cell. -/
theorem rlpWriteHeaderTail_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D N B0 w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hb : s.locals.lookup (ofString "base") = some (.val (.word B0)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s rlpWriteHeaderTail).2.memory w = s.memory w := by
  rw [rlpWriteHeaderTail]
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "n")] = some [.val (.word N)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_be_len")
    [.val (.word N)] (sourceFunctionBody Guest.guestFn_rlp_be_len) _ .one
    (by rw [code]; exact rlpBeLen_exact_lookup N)
  have look' := look
  rw [code] at look'
  obtain ⟨_,_,hv⟩ := rlpBeLen_call_facts N (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one look'
  have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_be_len)).2.memory w = s.memory w :=
    window_of_memoryFrame rlpBeLen_memoryFrame (callEntryStateHOLFinite s callee) w
      (by rw [callEntryStateHOLFinite]; exact code)
  refine decCall_window s (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
    _ w [.val (.word N)] (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one argsEval look
    hbody ?_
  intro value base run hsh1 hsh2 k
  obtain ⟨L,rfl⟩ := shapeWord_of_one hsh1
  have hL : L.toNat ≤ 8 := by
    obtain ⟨N',hN',hle⟩ := rlpBeLen_returns_le_eight (callEntryStateHOLFinite s callee) N hv
      (.val (.word L)) (by rw [run])
    have hLN : L = N' := by
      injection hN' with h
      injection h with h
    simpa [hLN] using hle
  rw [run] at hbody
  have baseCode : base.code = originalRuntimeCode := by
    have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_be_len)).1
    rw [run] at met
    exact met.trans (by simpa [callEntryStateHOLFinite] using code)
  set cs := setVarHOLFinite (ofString "ll") (.val (.word L)) {base with clock := k, locals := s.locals}
  have hdst : cs.locals.lookup (ofString "dst") = some (.val (.word D)) :=
    lookup_setVar_ne _ (ofString "ll") (ofString "dst") _ _ (by decide) hd
  have hbas : cs.locals.lookup (ofString "base") = some (.val (.word B0)) :=
    lookup_setVar_ne _ (ofString "ll") (ofString "base") _ _ (by decide) hb
  have hn' : cs.locals.lookup (ofString "n") = some (.val (.word N)) :=
    lookup_setVar_ne _ (ofString "ll") (ofString "n") _ _ (by decide) hn
  have hll : cs.locals.lookup (ofString "ll") = some (.val (.word L)) :=
    lookup_setVar_eq _ (ofString "ll") _
  have csmem : cs.memory w = s.memory w := by
    simp only [cs,setVarHOLFinite]
    exact hbody
  have cscode : cs.code = originalRuntimeCode := by
    simp only [cs,setVarHOLFinite]
    exact baseCode
  exact (rlpWriteHeaderCont_window cs D B0 N L w out hdst hbas hn' hll hL cscode).trans csmem

#print axioms rlpWriteHeaderTail_window

end InitECandidate.Runtime
