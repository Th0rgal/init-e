import InitECandidate.Runtime.RlpEncodeBytesPrefix
import InitECandidate.Runtime.OriginalMemcpyCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The exact code lookup of `rlp_write_header` binds its three parameters. -/
theorem rlpWriteHeader_exact_lookup (D B N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_write_header")
      [.val (.word D),.val (.word B),.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_write_header,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64))
                  else if x = ofString "base" then some (.val (.word B))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_write_header_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpWriteHeader_exact_lookup

/-- A successful finite lookup of the installed `rlp_write_header` on three word arguments has the
installed body, a one-word return shape, and reads those words back under their parameter names. -/
theorem rlpWriteHeader_call_facts (D B N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_write_header") [.val (.word D),.val (.word B),.val (.word N)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_write_header ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "base") = some (.val (.word B)) ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpWriteHeader_exact_lookup D B N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpWriteHeader_call_facts

/-- The exact code lookup of `memcpy` binds its three parameters. -/
theorem memcpy_exact_lookup (D S N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "memcpy")
      [.val (.word D),.val (.word S),.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_memcpy,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64))
                  else if x = ofString "src" then some (.val (.word S))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_memcpy_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms memcpy_exact_lookup

/-- A successful finite lookup of the installed `memcpy` on three word arguments has the installed
body, a one-word return shape, and reads those words back under their parameter names. -/
theorem memcpy_call_facts (D S N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "memcpy") [.val (.word D),.val (.word S),.val (.word N)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_memcpy ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "src") = some (.val (.word S)) ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [memcpy_exact_lookup D S N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms memcpy_call_facts

/-- **The header-and-copy tail of `rlp_encode_bytes`.** The actual `rlp_write_header` writes the
string header of at most nine bytes at `dst`, the actual `memcpy` copies the `n` source bytes to
`dst + h` (inside the widened window because `h ≤ 9`), and the writer returns `h + n`.  Every word
outside the `9 + n` byte window at `dst` keeps its cell. -/
theorem rlpEncodeBytesTail_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D S N w : BitVec 64) (out : ¬ MWin D (9 + N.toNat) w)
    (small : N.toNat + 32 < 2 ^ 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hs : s.locals.lookup (ofString "src") = some (.val (.word S)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s rlpEncodeBytesTail).2.memory w = s.memory w := by
  rw [rlpEncodeBytesTail]
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")] =
      some [.val (.word D), .val (.word 128), .val (.word N)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hd,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_write_header")
    [.val (.word D), .val (.word 128), .val (.word N)]
    (sourceFunctionBody Guest.guestFn_rlp_write_header) _ .one
    (by rw [code]; exact rlpWriteHeader_exact_lookup D 128 N)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hdC,hbC,hnC⟩ := rlpWriteHeader_call_facts D 128 N _ _ _ look'
  have entryCode : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hdE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "dst")
      = some (.val (.word D)) := by rw [callEntryStateHOLFinite]; exact hdC
  have hbE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "base")
      = some (.val (.word 128)) := by rw [callEntryStateHOLFinite]; exact hbC
  have hnE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n")
      = some (.val (.word N)) := by rw [callEntryStateHOLFinite]; exact hnC
  have win : ¬ MWin D 9 w := mwin_mono (by omega) out
  have hbodyW : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_write_header)).2.memory w = s.memory w := by
    rw [← bodyEq]
    exact (rlpWriteHeader_window (callEntryStateHOLFinite s callee) D N 128 w win
      hdE hnE hbE entryCode).trans (by rw [callEntryStateHOLFinite])
  refine decCall_window s (ofString "h") .one (ofString "rlp_write_header")
    [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")] _ w
    [.val (.word D), .val (.word 128), .val (.word N)] _ callee .one argsEval look hbodyW ?_
  intro value base run hsh1 hsh2 k
  obtain ⟨H,rfl⟩ := shapeWord_of_one hsh1
  have hHle : H.toNat ≤ 9 := by
    obtain ⟨H',hH',hle⟩ := rlpWriteHeader_returns_le_nine (callEntryStateHOLFinite s callee) N
      entryCode (.val (.word H)) hnE (by rw [← bodyEq]; exact congrArg Prod.fst run)
    have hEq : H = H' := HolWordLab.word.inj (ValueHOL.val.inj hH')
    rw [← hEq] at hle
    exact hle
  have baseMem : base.memory w = s.memory w := by
    have hb := hbodyW
    rw [run] at hb
    exact hb
  have baseCode : base.code = originalRuntimeCode := by
    have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_write_header)).1
    rw [run] at met
    exact met.trans entryCode
  set cs := setVarHOLFinite (ofString "h") (.val (.word H)) {base with clock := k, locals := s.locals}
  have cdst : cs.locals.lookup (ofString "dst") = some (.val (.word D)) :=
    lookup_setVar_ne _ (ofString "h") (ofString "dst") _ _ (by decide) hd
  have ch : cs.locals.lookup (ofString "h") = some (.val (.word H)) :=
    lookup_setVar_eq _ (ofString "h") _
  have hsrc : cs.locals.lookup (ofString "src") = some (.val (.word S)) :=
    lookup_setVar_ne _ (ofString "h") (ofString "src") _ _ (by decide) hs
  have cn : cs.locals.lookup (ofString "n") = some (.val (.word N)) :=
    lookup_setVar_ne _ (ofString "h") (ofString "n") _ _ (by decide) hn
  have csmem : cs.memory w = s.memory w := by
    simp only [cs,setVarHOLFinite]
    exact baseMem
  have cscode : cs.code = originalRuntimeCode := by
    simp only [cs,setVarHOLFinite]
    exact baseCode
  have hargs : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F'), t.locals = cs.locals →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
         .var .local (ofString "src"), .var .local (ofString "n")] =
        some [.val (.word (D + H)), .val (.word S), .val (.word N)] := by
    intro F' t ht
    have h1 : t.locals.lookup (ofString "dst") = some (.val (.word D)) := by rw [ht]; exact cdst
    have h2 : t.locals.lookup (ofString "h") = some (.val (.word H)) := by rw [ht]; exact ch
    have h3 : t.locals.lookup (ofString "src") = some (.val (.word S)) := by rw [ht]; exact hsrc
    have h4 : t.locals.lookup (ofString "n") = some (.val (.word N)) := by rw [ht]; exact cn
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,h1,h2,h3,h4,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨callee2,look2⟩ := lookupCodeHOLFinite_of_exact cs.code.lookup (ofString "memcpy")
    [.val (.word (D + H)), .val (.word S), .val (.word N)]
    (sourceFunctionBody Guest.guestFn_memcpy) _ .one
    (by rw [cscode]; exact memcpy_exact_lookup (D + H) S N)
  have look2' := look2
  rw [cscode] at look2'
  obtain ⟨bodyEq2,hshapeEq2,hd2,hs2,hn2⟩ := memcpy_call_facts (D + H) S N _ _ _ look2'
  have mwin : ¬ MWin (D + H) N.toNat w := fun hw => out (mwin_shift_word hHle hw)
  have bodyW2 : (evaluateHOLFiniteState (callEntryStateHOLFinite cs callee2)
      (sourceFunctionBody Guest.guestFn_memcpy)).2.memory w = cs.memory w := by
    have e1 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "dst")
        = some (.val (.word (D + H))) := by rw [callEntryStateHOLFinite]; exact hd2
    have e2 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "src")
        = some (.val (.word S)) := by rw [callEntryStateHOLFinite]; exact hs2
    have e3 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "n")
        = some (.val (.word N)) := by rw [callEntryStateHOLFinite]; exact hn2
    rw [← bodyEq2]
    exact (memcpy_body_window (callEntryStateHOLFinite cs callee2) (D + H) S N w e1 e2 e3
      small mwin).trans (by rw [callEntryStateHOLFinite])
  have callW : (evaluateHOLFiniteState cs (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
       .var .local (ofString "src"), .var .local (ofString "n")])).2.memory w = cs.memory w :=
    discardCall_window cs (ofString "memcpy") _ _ (sourceFunctionBody Guest.guestFn_memcpy)
      callee2 .one w (hargs cs rfl) look2 bodyW2
  exact (window_seq cs w callW (fun t ht =>
    (return_memory t (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) w).trans ht)).trans csmem

#print axioms rlpEncodeBytesTail_window

end InitECandidate.Runtime
