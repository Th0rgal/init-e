import InitECandidate.Runtime.RlpEncodeListHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- An `if` whose only returning branch is `return 1` only ever returns `1`. -/
theorem iteReturnOne_returns_one {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (r : ValueHOL 64)
    (run : (evaluateHOLFiniteState s (.ite cond (.return (.const (1#64))) .skip)).1 =
      some (.returned r)) : r = .val (.word (1#64)) := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      simp at run
    · rw [if_neg hz,evaluateHOLFiniteState_return] at run
      simp only [evalHOLExact] at run
      split at run
      · injection run with h
        injection h with h
        exact h.symm
      · simp at run
  · simp at run

#print axioms iteReturnOne_returns_one

/-- An `if` whose only returning branch is `return 1` continues only unchanged. -/
theorem iteReturnOne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (.ite cond (.return (.const (1#64))) .skip) = (none, mid)) :
    mid = s := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      obtain ⟨_,h⟩ := Prod.mk.inj run
      exact h.symm
    · rw [if_neg hz,evaluateHOLFiniteState_return] at run
      simp only [evalHOLExact] at run
      split at run <;> simp at run
  · obtain ⟨_,h⟩ := Prod.mk.inj run
    exact h.symm

#print axioms iteReturnOne_none

/-- The exact code lookup of `rlp_header_len` binds its single parameter `n`. -/
theorem rlpHeaderLen_exact_lookup (N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_header_len")
      [.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_header_len,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_header_len_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpHeaderLen_exact_lookup

/-- A successful finite lookup of the installed `rlp_header_len` on one word argument has the
installed body, a one-word return shape, and reads that word back as `n`. -/
theorem rlpHeaderLen_call_facts (N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_header_len") [.val (.word N)] = some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_header_len ∧ returnShape = .one ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpHeaderLen_exact_lookup N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp

#print axioms rlpHeaderLen_call_facts

/-- The exact code lookup of `rlp_list_header_len` binds its parameter `payload_len`. -/
theorem rlpListHeaderLen_exact_lookup (P : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_list_header_len")
      [.val (.word P)] =
      some (sourceFunctionBody Guest.guestFn_rlp_list_header_len,
        (fun x => if x = ofString "payload_len" then (some (.val (.word P)) : Option (ValueHOL 64)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_list_header_len_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpListHeaderLen_exact_lookup

/-- A successful finite lookup of the installed `rlp_list_header_len` on one word argument has the
installed body, a one-word return shape, and reads that word back as `payload_len`. -/
theorem rlpListHeaderLen_call_facts (P : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_list_header_len") [.val (.word P)] = some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_list_header_len ∧ returnShape = .one ∧
      callee.lookup (ofString "payload_len") = some (.val (.word P)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpListHeaderLen_exact_lookup P] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp

#print axioms rlpListHeaderLen_call_facts


/-- The `rlp_be_len` tail of `rlp_header_len` returns `1 + ll`, a word of at most nine bytes. -/
theorem rlpBeLenTail_returns_le_nine {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (run : (evaluateHOLFiniteState s (.decCall (ofString "ll") .one (ofString "rlp_be_len")
      [.var .local (ofString "n")]
      (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "n")] = some [.val (.word N)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_be_len")
    [.val (.word N)] (sourceFunctionBody Guest.guestFn_rlp_be_len) _ .one
    (by rw [code]; exact rlpBeLen_exact_lookup N)
  have look' := look
  rw [code] at look'
  cases decRun : evaluateHOLFiniteState s
      (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
        (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))) with
  | mk fres fpost =>
    rw [decRun] at run
    cases fres with
    | none => cases run
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr] at *
        obtain ⟨lengthValue,bodyPost,ready,output,bodyRun,readyLoc,_,_,_,readyCode,tail,_⟩ :=
          evaluate_decCall_returned_global_scope s fpost (ofString "ll") (ofString "rlp_be_len")
            .one .one [.var .local (ofString "n")] [.val (.word N)]
            (sourceFunctionBody Guest.guestFn_rlp_be_len) _ callee v argsEval look decRun
        obtain ⟨_,_,hv⟩ := rlpBeLen_call_facts N
          (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one look'
        obtain ⟨L, hL, hLle⟩ := rlpBeLen_returns_le_eight (callEntryStateHOLFinite s callee) N
          (by simpa [callEntryStateHOLFinite] using hv) lengthValue (by rw [bodyRun])
        rw [hL] at bodyRun tail
        have hllNew : ((setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L))
            ready).locals).lookup (ofString "ll") = some (ValueHOL.val (HolWordLab.word L)) :=
          lookup_setVar_eq _ (ofString "ll") _
        have hcont : evaluateHOLFiniteState
            (setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L)) ready)
            (.return (.op .add [.const (1#64), .var .local (ofString "ll")])) =
            (some (.returned v), output) := tail
        rw [evaluateHOLFiniteState_return] at hcont
        have exprEval : @evalHOLExact 64 F _
            (setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L)) ready).toExact
            (fun a => Classical.propDecidable
              ((setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L)) ready).memaddrs a))
            (.op .add [.const (1#64), .var .local (ofString "ll")]) =
            some (.val (.word (1#64 + L))) := by
          simp [evalHOLExact,evalListHOLExact,hllNew,wordOpHOL,wordOp,valueIsWord,valueWord]
        rw [exprEval] at hcont
        dsimp only at hcont
        split at hcont
        · injection hcont with h1 _
          injection h1 with h2
          injection h2 with h3
          refine ⟨1#64 + L, h3.symm, ?_⟩
          have eq : (1#64 + L).toNat = 1 + L.toNat := by
            rw [BitVec.toNat_add]
            simp
            omega
          omega
        · simp at hcont
      | _ => simp at run

#print axioms rlpBeLenTail_returns_le_nine

/-- **The actual `rlp_header_len` returns a word of at most nine bytes**: either the single length
byte of the short-header shortcut or `1 + ll` with the byte count `ll` at most eight. -/
theorem rlpHeaderLen_returns_le_nine {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (run : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_header_len)).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  rw [source_rlpHeaderLen_body] at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases pRun : evaluateHOLFiniteState s
      (.ite (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
        (.return (.const (1#64))) .skip) with
  | mk rp mp =>
    rw [pRun] at run
    dsimp only at run
    cases rp with
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr]
        refine ⟨1#64, iteReturnOne_returns_one s
          (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) v ?_, by decide⟩
        show (evaluateHOLFiniteState s
          (.ite (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
            (.return (.const (1#64))) .skip)).1 = some (.returned v)
        rw [pRun]
      | _ => simp at run
    | none =>
      have pEq := iteReturnOne_none s
        (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) mp pRun
      rw [pEq] at run
      dsimp only at run
      exact rlpBeLenTail_returns_le_nine s N code r hn run

#print axioms rlpHeaderLen_returns_le_nine

/-- **The actual `rlp_list_header_len` returns a word of at most nine bytes.**  It is one tail call
into the actual `rlp_header_len`. -/
theorem rlpListHeaderLen_returns_le_nine {F : Type} (s : PanSemStateFiniteExact 64 F)
    (P : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hp : s.locals.lookup (ofString "payload_len") = some (.val (.word P)))
    (run : (evaluateHOLFiniteState s
      (sourceFunctionBody Guest.guestFn_rlp_list_header_len)).1 = some (.returned r)) :
    ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  rw [source_rlpListHeaderLen_body] at run
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "payload_len")] = some [.val (.word P)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_header_len")
    [.val (.word P)] (sourceFunctionBody Guest.guestFn_rlp_header_len) _ .one
    (by rw [code]; exact rlpHeaderLen_exact_lookup P)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hnC⟩ := rlpHeaderLen_call_facts P _ callee .one look'
  have entryCode : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hnE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n")
      = some (.val (.word P)) := by rw [callEntryStateHOLFinite]; exact hnC
  rw [evaluateHOLFiniteState_call,argsEval] at run
  dsimp only at run
  rw [look] at run
  dsimp only at run
  split at run
  · simp at run
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
        (sourceFunctionBody Guest.guestFn_rlp_header_len) with
    | mk rb st =>
      rw [bodyRun] at run
      cases rb with
      | none => simp at run
      | some rr =>
        cases rr with
        | returned value =>
          dsimp only at run
          split at run
          · rename_i hshape
            have hrun : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
                (sourceFunctionBody Guest.guestFn_rlp_header_len)).1 = some (.returned value) := by
              rw [bodyRun]
            obtain ⟨H,hH,hle⟩ := rlpHeaderLen_returns_le_nine (callEntryStateHOLFinite s callee)
              P entryCode value hnE hrun
            have hvr : value = r := PanSemResultExact.returned.inj (Option.some.inj run)
            rw [← hvr]
            exact ⟨H,hH,hle⟩
          · simp at run
        | _ => simp at run

#print axioms rlpListHeaderLen_returns_le_nine

end InitECandidate.Runtime
