import InitECandidate.Runtime.RlpWriteHeaderContWindow
import InitECandidate.Runtime.RlpCalleeValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- **The long-header tail shared by `rlp_write_header` and `rlp_encode_word`.**  The actual
`rlp_be_len` call counts the bytes of a local word (binding it as `v`, no memory written), the length
byte is stored at `dst`, and the byte count goes to `dst + 1` through the actual `rlp_put_be`.  All
writes stay inside the nine-byte window at `dst`. -/
theorem rlpLongTailDecCall_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D W0 w : BitVec 64) (out : ¬ MWin D 9 w)
    (value : ExpHOL 64) (name : MlS) (hname : name ≠ ofString "ll")
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup name = some (.val (.word W0)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (.decCall (ofString "ll") .one (ofString "rlp_be_len")
      [.var .local name]
      (.seq (.storeByte (.var .local (ofString "dst")) value)
        (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           .var .local name, .var .local (ofString "ll")])
          (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))))).2.memory w =
      s.memory w := by
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local name] = some [.val (.word W0)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_be_len")
    [.val (.word W0)] (sourceFunctionBody Guest.guestFn_rlp_be_len) _ .one
    (by rw [code]; exact rlpBeLen_exact_lookup W0)
  have look' := look
  rw [code] at look'
  obtain ⟨_,_,hv⟩ := rlpBeLen_call_facts W0 (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one look'
  have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_be_len)).2.memory w = s.memory w :=
    window_of_memoryFrame rlpBeLen_memoryFrame (callEntryStateHOLFinite s callee) w
      (by rw [callEntryStateHOLFinite]; exact code)
  refine decCall_window s (ofString "ll") .one (ofString "rlp_be_len") [.var .local name]
    _ w [.val (.word W0)] (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one argsEval look
    hbody ?_
  intro value' base run hsh1 hsh2 k
  obtain ⟨L,rfl⟩ := shapeWord_of_one hsh1
  have hL : L.toNat ≤ 8 := by
    obtain ⟨N',hN',hle⟩ := rlpBeLen_returns_le_eight (callEntryStateHOLFinite s callee) W0 hv
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
  have hn' : cs.locals.lookup name = some (.val (.word W0)) :=
    lookup_setVar_ne _ (ofString "ll") name _ _ hname.symm hn
  have hll : cs.locals.lookup (ofString "ll") = some (.val (.word L)) :=
    lookup_setVar_eq _ (ofString "ll") _
  have csmem : cs.memory w = s.memory w := by
    simp only [cs,setVarHOLFinite]
    exact hbody
  have cscode : cs.code = originalRuntimeCode := by
    simp only [cs,setVarHOLFinite]
    exact baseCode
  have hargs : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F'), t.locals = cs.locals →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .const (1#64)],
         .var .local name, .var .local (ofString "ll")] =
        some [.val (.word (D + 1#64)),.val (.word W0),.val (.word L)] := by
    intro F' t ht
    have hdstT : t.locals.lookup (ofString "dst") = some (.val (.word D)) := by
      rw [ht]; exact hdst
    have hnT : t.locals.lookup name = some (.val (.word W0)) := by
      rw [ht]; exact hn'
    have hllT : t.locals.lookup (ofString "ll") = some (.val (.word L)) := by
      rw [ht]; exact hll
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hdstT,hnT,hllT,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  exact (rlpLongTail_window cs D L W0 w out value (.var .local name) hdst hll hargs hL cscode).trans csmem

#print axioms rlpLongTailDecCall_window

end InitECandidate.Runtime
