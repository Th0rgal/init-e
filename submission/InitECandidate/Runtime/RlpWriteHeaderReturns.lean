import InitECandidate.Runtime.RlpEncodeBytesUtil
import InitECandidate.Runtime.RlpWriteHeaderMemoryWindow
import InitECandidate.Runtime.PanDecCallReturnedGlobalScope
import InitECandidate.Runtime.HtabCopyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A single byte store only ever fails with an error. -/
theorem storeByte_result_error {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (res : PanSemResultExact 64) (st : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (.storeByte destination value) = (some res, st)) : res = .error := by
  have control := evaluate_storeByte_control_frame s destination value
  rw [run] at control
  dsimp only at control
  rcases control.1 with h | h
  · simp at h
  · exact Option.some.inj h

#print axioms storeByte_result_error

/-- The long-header continuation returns exactly the total length `1 + ll`. -/
theorem rlpLongTailCont_returns {F : Type} (cs : PanSemStateFiniteExact 64 F)
    (L : BitVec 64) (r : ValueHOL 64) (stored vExp : ExpHOL 64)
    (hll : cs.locals.lookup (ofString "ll") = some (.val (.word L)))
    (run : (evaluateHOLFiniteState cs (.seq
      (.storeByte (.var .local (ofString "dst")) stored)
      (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           vExp, .var .local (ofString "ll")])
        (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))).1 =
      some (.returned r)) : r = .val (.word (1#64 + L)) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases storeRun : evaluateHOLFiniteState cs (.storeByte (.var .local (ofString "dst")) stored) with
  | mk sr sp =>
    rw [storeRun] at run
    dsimp only at run
    have control := evaluate_storeByte_control_frame cs (.var .local (ofString "dst")) stored
    rw [storeRun] at control
    have spLoc : sp.locals = cs.locals := control.2.2.1
    cases sr with
    | none =>
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases callRun : evaluateHOLFiniteState sp (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           vExp, .var .local (ofString "ll")]) with
      | mk rc spc =>
        rw [callRun] at run
        dsimp only at run
        cases rc with
        | none =>
          have spcLoc : spc.locals = sp.locals := discard_call_normal_locals sp spc _ _ callRun
          have hll' : spc.locals.lookup (ofString "ll") = some (.val (.word L)) := by
            rw [spcLoc, spLoc]; exact hll
          rw [evaluateHOLFiniteState_return] at run
          dsimp only at run
          have exprEval : @evalHOLExact 64 F _ spc.toExact
              (fun a => Classical.propDecidable (spc.memaddrs a))
              (.op .add [.const (1#64), .var .local (ofString "ll")]) =
                some (.val (.word (1#64 + L))) := by
            simp [evalHOLExact,evalListHOLExact,hll',wordOpHOL,wordOp,valueIsWord,valueWord]
          rw [exprEval] at run
          dsimp only at run
          split at run
          · injection run with h
            injection h with h
            exact h.symm
          · simp at run
        | some rc' =>
          have hrc : rc' = .returned r := by simpa using run
          exfalso
          refine discard_call_not_returned sp (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const (1#64)],
             vExp, .var .local (ofString "ll")] r ?_
          rw [callRun]
          simp [hrc]
    | some res =>
      have hres := storeByte_result_error cs (.var .local (ofString "dst")) stored res sp storeRun
      subst hres
      simp at run

#print axioms rlpLongTailCont_returns

/-- The long-header tail of the RLP writers returns a word of at most nine bytes. -/
theorem rlpLongTailDecCall_returns {F : Type} (s : PanSemStateFiniteExact 64 F)
    (W0 : BitVec 64) (stored : ExpHOL 64) (name : MlS)
    (hn : s.locals.lookup name = some (.val (.word W0)))
    (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (run : (evaluateHOLFiniteState s (.decCall (ofString "ll") .one (ofString "rlp_be_len")
      [.var .local name]
      (.seq (.storeByte (.var .local (ofString "dst")) stored)
        (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           .var .local name, .var .local (ofString "ll")])
          (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))))).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local name] = some [.val (.word W0)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_be_len")
    [.val (.word W0)] (sourceFunctionBody Guest.guestFn_rlp_be_len) _ .one
    (by rw [code]; exact rlpBeLen_exact_lookup W0)
  have look' := look
  rw [code] at look'
  cases decRun : evaluateHOLFiniteState s
      (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local name]
        (.seq (.storeByte (.var .local (ofString "dst")) stored)
          (.seq (.call (some (none,none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const (1#64)],
             .var .local name, .var .local (ofString "ll")])
            (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))) with
  | mk fres fpost =>
    rw [decRun] at run
    cases fres with
    | none => cases run
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr] at *
        obtain ⟨lengthValue, bodyPost, ready, output, bodyRun, readyLoc, _, _, _, readyCode, tail, _⟩ :=
          evaluate_decCall_returned_global_scope s fpost (ofString "ll") (ofString "rlp_be_len")
            .one .one [.var .local name] [.val (.word W0)]
            (sourceFunctionBody Guest.guestFn_rlp_be_len) _ callee v argsEval look decRun
        obtain ⟨_,_,hv⟩ := rlpBeLen_call_facts W0
          (sourceFunctionBody Guest.guestFn_rlp_be_len) callee .one look'
        obtain ⟨L, hL, hLle⟩ := rlpBeLen_returns_le_eight (callEntryStateHOLFinite s callee) W0
          (by simpa [callEntryStateHOLFinite] using hv) lengthValue (by rw [bodyRun])
        rw [hL] at bodyRun tail
        have hllNew : ((setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L))
            ready).locals).lookup (ofString "ll") = some (ValueHOL.val (HolWordLab.word L)) :=
          lookup_setVar_eq _ (ofString "ll") _
        have contRun : (evaluateHOLFiniteState
            (setVarHOLFinite (ofString "ll") (ValueHOL.val (HolWordLab.word L)) ready)
            (.seq (.storeByte (.var .local (ofString "dst")) stored)
              (.seq (.call (some (none,none)) (ofString "rlp_put_be")
                [.op .add [.var .local (ofString "dst"), .const (1#64)],
                 .var .local name, .var .local (ofString "ll")])
                (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))).1 =
            some (.returned v) := by rw [tail]
        have hval := rlpLongTailCont_returns _ L v stored (.var .local name) hllNew contRun
        refine ⟨1#64 + L, hval, ?_⟩
        have eq : (1#64 + L).toNat = 1 + L.toNat := by
          rw [BitVec.toNat_add]
          simp
          omega
        omega
      | _ => simp at run

#print axioms rlpLongTailDecCall_returns

/-- **The actual `rlp_write_header` returns a word of at most nine bytes**: either the single
short-header byte or the long-header continuation `1 + ll` with the byte count `ll` at most eight. -/
theorem rlpWriteHeader_returns_le_nine {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (run : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_write_header)).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  rw [source_rlpWriteHeader_body] at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases pRun : evaluateHOLFiniteState s rlpWriteHeaderPrefix with
  | mk rp mp =>
    rw [pRun] at run
    dsimp only at run
    cases rp with
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr]
        have hone := bytePrefix_returns_one s
          (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
          (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) v
          (by show (evaluateHOLFiniteState s rlpWriteHeaderPrefix).1 = some (.returned v)
              rw [pRun])
        exact ⟨1#64, hone, by decide⟩
      | _ => simp at run
    | none =>
      have pEq := rlpWriteHeaderPrefix_none s N hn mp pRun
      rw [pEq] at run
      dsimp only at run
      rw [rlpWriteHeaderTail] at run
      exact rlpLongTailDecCall_returns s N
        (.op .add [.var .local (ofString "base"), .const (55#64), .var .local (ofString "ll")])
        (ofString "n") hn code r run

#print axioms rlpWriteHeader_returns_le_nine

end InitECandidate.Runtime
