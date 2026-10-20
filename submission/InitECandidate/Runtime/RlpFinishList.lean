import InitECandidate.Runtime.RlpHeaderLenReturns
import InitECandidate.Runtime.OriginalRlpWriterCode
import InitECandidate.Proofs.FrontendStages.Declarations.Agreement125
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendStages.Declarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-- The installed code entry of `rlp_encode_list_header` with its two word parameters. -/
theorem originalRuntimeCode_rlp_encode_list_header_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_list_header") =
      some ([(ofString "dst",.one),(ofString "payload_len",.one)],
        sourceFunctionBody Guest.guestFn_rlp_encode_list_header,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_encode_list_header")
    (originals.take 125) original125 (originals.drop 126)
    [(ofString "dst",.one),(ofString "payload_len",.one)]
    (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original125_eq]
    simp only [Guest.guestFn_rlp_encode_list_header,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_encode_list_header_lookup

/-- The exact code lookup of `rlp_encode_list_header` binds its two parameters. -/
theorem rlpEncodeListHeader_exact_lookup (D N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_encode_list_header")
      [.val (.word D),.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_encode_list_header,
        (fun x => if x = ofString "payload_len" then (some (.val (.word N)) : Option (ValueHOL 64))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_encode_list_header_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpEncodeListHeader_exact_lookup

/-- A successful finite lookup of the installed `rlp_encode_list_header` on two word arguments has
the installed body, a one-word return shape, and reads those words back under their names. -/
theorem rlpEncodeListHeader_call_facts (D N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_encode_list_header") [.val (.word D),.val (.word N)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_encode_list_header ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "payload_len") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpEncodeListHeader_exact_lookup D N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpEncodeListHeader_call_facts

/-- The payload length initializer of `rlp_finish_list`: `payload_end - (dst + 9)`. -/
def rlpFinishListPayloadInit : ExpHOL 64 :=
  .op .sub [.var .local (ofString "payload_end"),
    .op .add [.var .local (ofString "dst"), .const (9#64)]]

/-- The remaining body of `rlp_finish_list`: measure the list header, copy the payload up to sit
right after the nine-byte header slot, write the list header, and return the total size. -/
def rlpFinishListTorso : ProgHOL 64 :=
  .decCall (ofString "hl") .one (ofString "rlp_list_header_len") [.var .local (ofString "payload")]
    (.seq (.call (some (none,none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
         .op .add [.var .local (ofString "dst"), .const (9#64)],
         .var .local (ofString "payload")])
      (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header")
          [.var .local (ofString "dst"), .var .local (ofString "payload")])
        (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]))))

/-- The body equation of the actual `rlp_finish_list`. -/
theorem source_rlpFinishList_body :
    sourceFunctionBody Guest.guestFn_rlp_finish_list =
      .dec (ofString "payload") .one rlpFinishListPayloadInit rlpFinishListTorso := by
  rw [rlpFinishListPayloadInit,rlpFinishListTorso]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpFinishList_body

/-- A discarded call followed by a program keeps the watched cell when the call keeps it and the
program keeps it from any state with the caller locals and code. -/
theorem discardCall_seq_window {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (function : MlS) (arguments : List (ExpHOL 64)) {second : ProgHOL 64}
    (h1 : (evaluateHOLFiniteState s (.call (some (none,none)) function arguments)).2.memory w =
      s.memory w)
    (h2 : ∀ (t : PanSemStateFiniteExact 64 F), t.locals = s.locals → t.code = s.code →
      t.memory w = s.memory w → (evaluateHOLFiniteState t second).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) function arguments) second)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState s (.call (some (none,none)) function arguments) with
  | mk r middle =>
    rw [run] at h1
    cases r with
    | none =>
      dsimp only
      have hcode : middle.code = s.code := by
        have met := (evaluateHOLFiniteState_metadata s
          (.call (some (none,none)) function arguments)).1
        rw [run] at met
        exact met
      exact h2 middle (discard_call_normal_locals s middle function arguments run) hcode h1
    | some res => exact h1

#print axioms discardCall_seq_window

/-- The copy-then-header tail of `rlp_finish_list` keeps cells outside the nine-byte window. -/
theorem rlpFinishListTail_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (D P w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : t.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hp : t.locals.lookup (ofString "payload") = some (.val (.word P)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t
      (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header")
          [.var .local (ofString "dst"), .var .local (ofString "payload")])
        (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")])))).2.memory w =
      t.memory w := by
  have argsEval : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.var .local (ofString "dst"), .var .local (ofString "payload")] =
      some [.val (.word D), .val (.word P)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hd,hp]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact t.code.lookup
    (ofString "rlp_encode_list_header") [.val (.word D), .val (.word P)]
    (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) _ .one
    (by rw [code]; exact rlpEncodeListHeader_exact_lookup D P)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hdC,hnC⟩ := rlpEncodeListHeader_call_facts D P _ _ _ look'
  have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
      = some (.val (.word D)) := by rw [callEntryStateHOLFinite]; exact hdC
  have hnE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "payload_len")
      = some (.val (.word P)) := by rw [callEntryStateHOLFinite]; exact hnC
  have bodyW : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
      (sourceFunctionBody Guest.guestFn_rlp_encode_list_header)).2.memory w = t.memory w := by
    rw [← bodyEq]
    exact (rlpEncodeListHeader_window (callEntryStateHOLFinite t callee) D P w out
      hdE hnE entryCode).trans (by rw [callEntryStateHOLFinite])
  have callW := discardCall_window t (ofString "rlp_encode_list_header")
    [.var .local (ofString "dst"), .var .local (ofString "payload")]
    [.val (.word D), .val (.word P)]
    (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) callee .one w argsEval look bodyW
  exact (window_seq t w callW (fun u hu =>
    (return_memory u (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]) w).trans hu))

#print axioms rlpFinishListTail_window

/-- The body of `rlp_finish_list` after the payload length binding keeps cells outside the
`9 + payload` byte window at `dst`. -/
theorem rlpFinishListTorso_window {F : Type} (bs : PanSemStateFiniteExact 64 F)
    (D P w : BitVec 64) (out : ¬ MWin D (9 + P.toNat) w)
    (small : P.toNat + 32 < 2 ^ 64)
    (hd : bs.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hp : bs.locals.lookup (ofString "payload") = some (.val (.word P)))
    (code : bs.code = originalRuntimeCode) :
    (evaluateHOLFiniteState bs rlpFinishListTorso).2.memory w = bs.memory w := by
  rw [rlpFinishListTorso]
  have argsEval : evalListHOLFinite bs (h := fun a => Classical.propDecidable (bs.memaddrs a))
      [.var .local (ofString "payload")] = some [.val (.word P)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact bs.code.lookup
    (ofString "rlp_list_header_len") [.val (.word P)]
    (sourceFunctionBody Guest.guestFn_rlp_list_header_len) _ .one
    (by rw [code]; exact rlpListHeaderLen_exact_lookup P)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hpC⟩ := rlpListHeaderLen_call_facts P _ callee .one look'
  have entryCode : (callEntryStateHOLFinite bs callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hpE : (callEntryStateHOLFinite bs callee).locals.lookup (ofString "payload_len")
      = some (.val (.word P)) := by rw [callEntryStateHOLFinite]; exact hpC
  have hbodyW : (evaluateHOLFiniteState (callEntryStateHOLFinite bs callee)
      (sourceFunctionBody Guest.guestFn_rlp_list_header_len)).2.memory w = bs.memory w := by
    rw [← bodyEq]
    exact (window_of_memoryFrame rlpListHeaderLen_memoryFrame
      (callEntryStateHOLFinite bs callee) w entryCode).trans (by rw [callEntryStateHOLFinite])
  refine decCall_window bs (ofString "hl") .one (ofString "rlp_list_header_len")
    [.var .local (ofString "payload")] _ w [.val (.word P)] _ callee .one argsEval look hbodyW ?_
  intro value base run hsh1 hsh2 k
  obtain ⟨H,rfl⟩ := shapeWord_of_one hsh1
  have hHle : H.toNat ≤ 9 := by
    obtain ⟨H',hH',hle⟩ := rlpListHeaderLen_returns_le_nine (callEntryStateHOLFinite bs callee)
      P entryCode (.val (.word H)) hpE (by rw [← bodyEq]; exact congrArg Prod.fst run)
    have hEq : H = H' := HolWordLab.word.inj (ValueHOL.val.inj hH')
    rw [← hEq] at hle
    exact hle
  have baseMem : base.memory w = bs.memory w := by
    have hb := hbodyW
    rw [run] at hb
    exact hb
  have baseCode : base.code = originalRuntimeCode := by
    have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite bs callee)
      (sourceFunctionBody Guest.guestFn_rlp_list_header_len)).1
    rw [run] at met
    exact met.trans entryCode
  set cs := setVarHOLFinite (ofString "hl") (.val (.word H)) {base with clock := k, locals := bs.locals}
  have cdst : cs.locals.lookup (ofString "dst") = some (.val (.word D)) :=
    lookup_setVar_ne _ (ofString "hl") (ofString "dst") _ _ (by decide) hd
  have cpay : cs.locals.lookup (ofString "payload") = some (.val (.word P)) :=
    lookup_setVar_ne _ (ofString "hl") (ofString "payload") _ _ (by decide) hp
  have chl : cs.locals.lookup (ofString "hl") = some (.val (.word H)) :=
    lookup_setVar_eq _ (ofString "hl") _
  have csmem : cs.memory w = bs.memory w := by
    simp only [cs,setVarHOLFinite]
    exact baseMem
  have cscode : cs.code = originalRuntimeCode := by
    simp only [cs,setVarHOLFinite]
    exact baseCode
  have hargs : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F'), t.locals = cs.locals →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
         .op .add [.var .local (ofString "dst"), .const (9#64)],
         .var .local (ofString "payload")] =
        some [.val (.word (D + H)), .val (.word (D + 9#64)), .val (.word P)] := by
    intro F' t ht
    have h1 : t.locals.lookup (ofString "dst") = some (.val (.word D)) := by rw [ht]; exact cdst
    have h2 : t.locals.lookup (ofString "hl") = some (.val (.word H)) := by rw [ht]; exact chl
    have h3 : t.locals.lookup (ofString "payload") = some (.val (.word P)) := by rw [ht]; exact cpay
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,h1,h2,h3,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨callee2,look2⟩ := lookupCodeHOLFinite_of_exact cs.code.lookup (ofString "memcpy")
    [.val (.word (D + H)), .val (.word (D + 9#64)), .val (.word P)]
    (sourceFunctionBody Guest.guestFn_memcpy) _ .one
    (by rw [cscode]; exact memcpy_exact_lookup (D + H) (D + 9#64) P)
  have look2' := look2
  rw [cscode] at look2'
  obtain ⟨bodyEq2,hshapeEq2,hd2,hs2,hn2⟩ := memcpy_call_facts (D + H) (D + 9#64) P _ _ _ look2'
  have mwin : ¬ MWin (D + H) P.toNat w := fun hw => out (mwin_shift_word hHle hw)
  have bodyW2 : (evaluateHOLFiniteState (callEntryStateHOLFinite cs callee2)
      (sourceFunctionBody Guest.guestFn_memcpy)).2.memory w = cs.memory w := by
    have e1 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "dst")
        = some (.val (.word (D + H))) := by rw [callEntryStateHOLFinite]; exact hd2
    have e2 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "src")
        = some (.val (.word (D + 9#64))) := by rw [callEntryStateHOLFinite]; exact hs2
    have e3 : (callEntryStateHOLFinite cs callee2).locals.lookup (ofString "n")
        = some (.val (.word P)) := by rw [callEntryStateHOLFinite]; exact hn2
    rw [← bodyEq2]
    exact (memcpy_body_window (callEntryStateHOLFinite cs callee2) (D + H) (D + 9#64) P w
      e1 e2 e3 small mwin).trans (by rw [callEntryStateHOLFinite])
  have callW : (evaluateHOLFiniteState cs (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
       .op .add [.var .local (ofString "dst"), .const (9#64)],
       .var .local (ofString "payload")])).2.memory w = cs.memory w :=
    discardCall_window cs (ofString "memcpy") _ _ (sourceFunctionBody Guest.guestFn_memcpy)
      callee2 .one w (hargs cs rfl) look2 bodyW2
  have h2 : ∀ (t : PanSemStateFiniteExact 64 F), t.locals = cs.locals → t.code = cs.code →
      t.memory w = cs.memory w →
      (evaluateHOLFiniteState t
        (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header")
            [.var .local (ofString "dst"), .var .local (ofString "payload")])
          (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")])))).2.memory w =
        cs.memory w := by
    intro t ht hc hm
    have tdst : t.locals.lookup (ofString "dst") = some (.val (.word D)) := by rw [ht]; exact cdst
    have tpay : t.locals.lookup (ofString "payload") = some (.val (.word P)) := by rw [ht]; exact cpay
    have tcode : t.code = originalRuntimeCode := by rw [hc]; exact cscode
    have out9 : ¬ MWin D 9 w := mwin_mono (by omega) out
    exact (rlpFinishListTail_window t D P w out9 tdst tpay tcode).trans hm
  exact (discardCall_seq_window cs w (ofString "memcpy") _ callW h2).trans csmem

#print axioms rlpFinishListTorso_window

/-- **The actual `rlp_finish_list`** writes only inside the `9 + payload` byte window at `dst`:
the payload length `payload_end - (dst + 9)`, the actual list header length (at most nine bytes),
the payload copy into `dst + hl`, and the actual list header at `dst`. -/
theorem rlpFinishList_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D E P w : BitVec 64) (out : ¬ MWin D (9 + P.toNat) w)
    (small : P.toNat + 32 < 2 ^ 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (he : s.locals.lookup (ofString "payload_end") = some (.val (.word E)))
    (hpv : E - (D + 9#64) = P)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_finish_list)).2.memory w =
      s.memory w := by
  rw [source_rlpFinishList_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  have initEval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) rlpFinishListPayloadInit =
      some (.val (.word P)) := by
    simp [rlpFinishListPayloadInit,evalHOLExact,evalListHOLExact,hd,he,wordOpHOL,wordOp,
      valueIsWord,valueWord,hpv]
  rw [initEval]
  dsimp only
  split
  · rename_i hshape
    have bdst : (setVarHOLFinite (ofString "payload") (.val (.word P)) s).locals.lookup
        (ofString "dst") = some (.val (.word D)) :=
      lookup_setVar_ne _ (ofString "payload") (ofString "dst") _ _ (by decide) hd
    have bpay : (setVarHOLFinite (ofString "payload") (.val (.word P)) s).locals.lookup
        (ofString "payload") = some (.val (.word P)) :=
      lookup_setVar_eq _ (ofString "payload") _
    have bcode : (setVarHOLFinite (ofString "payload") (.val (.word P)) s).code =
        originalRuntimeCode := by
      simp only [setVarHOLFinite]
      exact code
    have bmem : (setVarHOLFinite (ofString "payload") (.val (.word P)) s).memory w = s.memory w := by
      simp only [setVarHOLFinite]
    have torso := rlpFinishListTorso_window
      (setVarHOLFinite (ofString "payload") (.val (.word P)) s) D P w out small bdst bpay bcode
    exact torso.trans bmem
  · rfl

#print axioms rlpFinishList_window

end InitECandidate.Runtime
