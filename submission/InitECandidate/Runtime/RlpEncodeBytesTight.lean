import InitECandidate.Runtime.RlpEncodeBytesReturns
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The short-header prefix of the actual `rlp_write_header` always produces a result when the
length fits the single-byte header: the comparison is decidable past `55`. -/
theorem rlpWriteHeaderPrefix_some_of_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hN : N.toNat ≤ 55) :
    ∃ r st, evaluateHOLFiniteState s rlpWriteHeaderPrefix = (some r, st) := by
  have h55 : (55#64 : BitVec 64).toNat = 55 := by decide
  have hlt : ¬ ((55#64) < N) := by
    intro h
    rw [BitVec.lt_def] at h
    omega
  rw [rlpWriteHeaderPrefix,evaluateHOLFiniteState_ite]
  have condEval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
    simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,decide_eq_false hlt]
  rw [condEval]
  dsimp only
  rw [if_neg (by decide : ¬ ((1#64 : BitVec 64) = 0))]
  exact storeReturn_some s
    (.var .local (ofString "dst"))
    (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])

#print axioms rlpWriteHeaderPrefix_some_of_le

/-- **The actual `rlp_write_header` returns the single length byte** whenever the length fits the
short header. -/
theorem rlpWriteHeader_returns_one_of_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hN : N.toNat ≤ 55)
    (run : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_write_header)).1 =
      some (.returned r)) : r = .val (.word (1#64)) := by
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
        exact bytePrefix_returns_one s
          (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
          (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) v
          (by show (evaluateHOLFiniteState s rlpWriteHeaderPrefix).1 = some (.returned v)
              rw [pRun])
      | _ => simp at run
    | _ =>
      obtain ⟨rr,ss,hss⟩ := rlpWriteHeaderPrefix_some_of_le s N hn hN
      rw [hss] at pRun
      simp at pRun

#print axioms rlpWriteHeader_returns_one_of_le

/-- The copy-and-return continuation of the actual `rlp_encode_bytes` returns `h + n`, so a
one-byte header bounds the result by `1 + n`. -/
theorem rlpEncodeBytesTailCont_returns_one_add {F : Type} (cs : PanSemStateFiniteExact 64 F)
    (D S N H : BitVec 64) (hH : H.toNat ≤ 1)
    (hd : cs.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hs : cs.locals.lookup (ofString "src") = some (.val (.word S)))
    (hn : cs.locals.lookup (ofString "n") = some (.val (.word N)))
    (ch : cs.locals.lookup (ofString "h") = some (.val (.word H)))
    (code : cs.code = originalRuntimeCode) (r : ValueHOL 64)
    (output : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState cs
      (.seq (.call (some (none,none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"), .var .local (ofString "n")])
        (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) =
      (some (.returned r),output)) : ∃ K : BitVec 64, r = .val (.word K) ∧ K.toNat ≤ 1 + N.toNat := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState cs (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
       .var .local (ofString "src"), .var .local (ofString "n")]) with
  | mk rc spc =>
    rw [callRun] at run
    dsimp only at run
    cases rc with
    | none =>
      rw [evaluateHOLFiniteState_return] at run
      dsimp only at run
      have spcLoc : spc.locals = cs.locals := discard_call_normal_locals cs spc _ _ callRun
      have hhv : spc.locals.lookup (ofString "h") = some (.val (.word H)) := by
        rw [spcLoc]; exact ch
      have hnv : spc.locals.lookup (ofString "n") = some (.val (.word N)) := by
        rw [spcLoc]; exact hn
      have exprEval : @evalHOLExact 64 F _ spc.toExact
          (fun a => Classical.propDecidable (spc.memaddrs a))
          (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
          some (.val (.word (H + N))) := by
        simp [evalHOLExact,evalListHOLExact,hhv,hnv,wordOpHOL,wordOp,valueIsWord,valueWord]
      rw [exprEval] at run
      simp only at run
      split at run
      · injection run with h1
        injection h1 with h2
        injection h2 with h3
        refine ⟨H + N, h3.symm, ?_⟩
        have eq : (H + N).toNat ≤ H.toNat + N.toNat := by
          rw [BitVec.toNat_add]
          exact Nat.mod_le _ _
        omega
      · simp at run
    | some res =>
      have hres : res = .returned r := Option.some.inj (Prod.mk.inj run).1
      have hne := discard_call_not_returned cs (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
         .var .local (ofString "src"), .var .local (ofString "n")] r
      rw [callRun] at hne
      exact absurd hres (by simpa using hne)

#print axioms rlpEncodeBytesTailCont_returns_one_add

/-- **The actual `rlp_encode_bytes` returns at most `1 + n` bytes** when the length fits the
single-byte header: one byte on the single-byte path, and a one-byte header plus `n` otherwise. -/
theorem rlpEncodeBytes_returns_le_one_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D S N : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hs : s.locals.lookup (ofString "src") = some (.val (.word S)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hN : N.toNat ≤ 55)
    (run : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 1 + N.toNat := by
  rw [source_rlpEncodeBytes_body] at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases pRun : evaluateHOLFiniteState s rlpEncodeBytesPrefix with
  | mk rp mp =>
    rw [pRun] at run
    dsimp only at run
    cases rp with
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr]
        have hone : (1#64).toNat = 1 := by decide
        refine ⟨1#64, rlpEncodeBytesPrefix_returns_one s v ?_, by omega⟩
        show (evaluateHOLFiniteState s rlpEncodeBytesPrefix).1 = some (.returned v)
        rw [pRun]
      | _ => simp at run
    | none =>
      dsimp only at run
      obtain ⟨_,pcodeRaw,_,ploc⟩ := rlpEncodeBytesPrefix_none s mp pRun
      have pcode : mp.code = originalRuntimeCode := pcodeRaw.trans code
      have hdM : mp.locals.lookup (ofString "dst") = some (.val (.word D)) := by
        rw [ploc (ofString "dst") (by decide)]; exact hd
      have hsM : mp.locals.lookup (ofString "src") = some (.val (.word S)) := by
        rw [ploc (ofString "src") (by decide)]; exact hs
      have hnM : mp.locals.lookup (ofString "n") = some (.val (.word N)) := by
        rw [ploc (ofString "n") (by decide)]; exact hn
      rw [rlpEncodeBytesTail] at run
      have argsEvalM : evalListHOLFinite mp (h := fun a => Classical.propDecidable (mp.memaddrs a))
          [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")] =
          some [.val (.word D), .val (.word 128), .val (.word N)] := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hdM,hnM]
      obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact mp.code.lookup
        (ofString "rlp_write_header")
        [.val (.word D), .val (.word 128), .val (.word N)]
        (sourceFunctionBody Guest.guestFn_rlp_write_header) _ .one
        (by rw [pcode]; exact rlpWriteHeader_exact_lookup D 128 N)
      have look' := look
      rw [pcode] at look'
      obtain ⟨bodyEq,hshapeEq,hdC,hbC,hnC⟩ := rlpWriteHeader_call_facts D 128 N _ _ _ look'
      have entryCode : (callEntryStateHOLFinite mp callee).code = originalRuntimeCode := by
        rw [callEntryStateHOLFinite]; exact pcode
      have hnE : (callEntryStateHOLFinite mp callee).locals.lookup (ofString "n")
          = some (.val (.word N)) := by rw [callEntryStateHOLFinite]; exact hnC
      cases decRun : evaluateHOLFiniteState mp
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")]
            (.seq (.call (some (none,none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"), .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) with
      | mk fres fpost =>
        rw [decRun] at run
        cases fres with
        | none => cases run
        | some res =>
          cases res with
          | returned v =>
            have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
            obtain ⟨hValue,bodyPost,ready,output,bodyRun,readyLoc,_,_,_,readyCode,tail,_⟩ :=
              evaluate_decCall_returned_global_scope mp fpost (ofString "h")
                (ofString "rlp_write_header") .one .one
                [.var .local (ofString "dst"), .const (128#64), .var .local (ofString "n")]
                [.val (.word D), .val (.word 128), .val (.word N)]
                (sourceFunctionBody Guest.guestFn_rlp_write_header) _ callee v argsEvalM look decRun
            have hone := rlpWriteHeader_returns_one_of_le
              (callEntryStateHOLFinite mp callee) N entryCode hValue hnE hN
              (congrArg Prod.fst bodyRun)
            rw [hone] at bodyRun tail
            rw [← hvr]
            set cs := setVarHOLFinite (ofString "h") (.val (.word (1#64))) ready
            have cdst : cs.locals.lookup (ofString "dst") = some (.val (.word D)) := by
              simp only [cs,setVarHOLFinite]
              rw [readyLoc]; exact hdM
            have csrc : cs.locals.lookup (ofString "src") = some (.val (.word S)) := by
              simp only [cs,setVarHOLFinite]
              rw [readyLoc]; exact hsM
            have cn : cs.locals.lookup (ofString "n") = some (.val (.word N)) := by
              simp only [cs,setVarHOLFinite]
              rw [readyLoc]; exact hnM
            have ch : cs.locals.lookup (ofString "h") = some (.val (.word (1#64))) := by
              simp only [cs,setVarHOLFinite]
              exact lookup_setVar_eq _ (ofString "h") _
            have bodyCode : bodyPost.code = originalRuntimeCode := by
              have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite mp callee)
                (sourceFunctionBody Guest.guestFn_rlp_write_header)).1
              rw [bodyRun] at met
              exact met.trans entryCode
            have ccode : cs.code = originalRuntimeCode := by
              simp only [cs,setVarHOLFinite]
              exact readyCode.trans bodyCode
            obtain ⟨K,hK,hKle⟩ := rlpEncodeBytesTailCont_returns_one_add cs D S N (1#64)
              (by decide) cdst csrc cn ch ccode v output (by rw [← tail])
            exact ⟨K,hK,hKle⟩
          | _ => simp at run

#print axioms rlpEncodeBytes_returns_le_one_add

end InitECandidate.Runtime
