import InitECandidate.Runtime.RlpEncodeWithdrawal
import InitECandidate.Runtime.RlpEncodeBytesTight
import InitECandidate.Runtime.RlpWindowShiftGeneral
import InitECandidate.Runtime.RlpWindowCalls
import InitECandidate.Runtime.RlpEncodeWordWindow
import InitECandidate.Runtime.RlpEncodeBytesWindow
import InitECandidate.Runtime.RlpPutBeWindow
import InitECandidate.Runtime.RlpCalleeValues
import InitECandidate.Runtime.AccountLeafAnyAlloc
import InitECandidate.Runtime.OriginalAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- The running-offset assignment of `encode_withdrawal_rlp`: `p := p + w`. -/
def wdAssign : ProgHOL 64 := .assign .local (ofString "p") withdrawalOffset

/-- The list-finishing tail of `encode_withdrawal_rlp`. -/
def wdFinishTail : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_finish_list")
    [.var .local (ofString "buf"), .var .local (ofString "p")]
    (.return (.rstruct [.var .local (ofString "buf"), .var .local (ofString "total")]))

/-- The assign and finish that follow the amount writer. -/
def wdCall36Tail : ProgHOL 64 := .seq wdAssign wdFinishTail

/-- The amount writer call. -/
def wdCall36 : ProgHOL 64 :=
  .call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
    [.var .local (ofString "p"), withdrawalWord36]

/-- The assign and amount writer that follow the address writer. -/
def wdCallBytesTail : ProgHOL 64 := .seq wdAssign (.seq wdCall36 wdCall36Tail)

/-- The address writer call. -/
def wdCallBytes : ProgHOL 64 :=
  .call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes")
    [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
     .const (20#64)]

/-- The assign and address writer that follow the second record word. -/
def wdCall8Tail : ProgHOL 64 := .seq wdAssign (.seq wdCallBytes wdCallBytesTail)

/-- The second record word writer call. -/
def wdCall8 : ProgHOL 64 :=
  .call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
    [.var .local (ofString "p"), withdrawalWord8]

/-- The assign and second record word that follow the first word writer. -/
def wdCall0Tail : ProgHOL 64 := .seq wdAssign (.seq wdCall8 wdCall8Tail)

/-- The first record word writer, a declared call binding `w`. -/
def wdCall0 : ProgHOL 64 :=
  .decCall (ofString "w") .one (ofString "rlp_encode_word")
    [.var .local (ofString "p"), withdrawalWord0] wdCall0Tail

/-- The writer-cursor initializer of `encode_withdrawal_rlp`. -/
def wdDecP : ProgHOL 64 :=
  .dec (ofString "p") .one (.op .add [.var .local (ofString "buf"), .const (9#64)]) wdCall0

/-- The whole body of `encode_withdrawal_rlp` headed by the buffer allocation. -/
def wdAllocTail : ProgHOL 64 :=
  .decCall (ofString "buf") .one (ofString "alloc") [(.const (64#64))] wdDecP

/-- The body of `encode_withdrawal_rlp` split into its allocation prefix and writer tail. -/
theorem rlpEncodeWithdrawal_eq :
    rlpEncodeWithdrawal = wdAllocTail := rfl

#print axioms rlpEncodeWithdrawal_eq

/-- The exact code lookup of `rlp_encode_word` binds its two word parameters. -/
theorem rlpEncodeWord_exact_lookup (D V : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_encode_word")
      [.val (.word D),.val (.word V)] =
      some (sourceFunctionBody Guest.guestFn_rlp_encode_word,
        (fun x => if x = ofString "w" then (some (.val (.word V)) : Option (ValueHOL 64))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_encode_word_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpEncodeWord_exact_lookup

/-- The exact code lookup of `rlp_encode_bytes` binds its three word parameters. -/
theorem rlpEncodeBytes_exact_lookup (D S N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_encode_bytes")
      [.val (.word D),.val (.word S),.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_encode_bytes,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64))
                  else if x = ofString "src" then some (.val (.word S))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_encode_bytes_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpEncodeBytes_exact_lookup

/-- The exact code lookup of `rlp_finish_list` binds its two word parameters. -/
theorem rlpFinishList_exact_lookup (D E : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_finish_list")
      [.val (.word D),.val (.word E)] =
      some (sourceFunctionBody Guest.guestFn_rlp_finish_list,
        (fun x => if x = ofString "payload_end" then (some (.val (.word E)) : Option (ValueHOL 64))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_finish_list_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpFinishList_exact_lookup

/-- **The actual `rlp_encode_word` call binds `dst` and `w`.** -/
theorem rlpEncodeWord_call_facts (D V : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_encode_word") [.val (.word D),.val (.word V)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_encode_word ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "w") = some (.val (.word V)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpEncodeWord_exact_lookup D V] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpEncodeWord_call_facts

/-- **The actual `rlp_encode_bytes` call binds `dst`, `src` and `n`.** -/
theorem rlpEncodeBytes_call_facts (D S N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_encode_bytes") [.val (.word D),.val (.word S),.val (.word N)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_encode_bytes ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "src") = some (.val (.word S)) ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpEncodeBytes_exact_lookup D S N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpEncodeBytes_call_facts

/-- **The actual `rlp_finish_list` call binds `dst` and `payload_end`.** -/
theorem rlpFinishList_call_facts (D E : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_finish_list") [.val (.word D),.val (.word E)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_finish_list ∧ returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "payload_end") = some (.val (.word E)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpFinishList_exact_lookup D E] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpFinishList_call_facts

/-- A successful result-binding call keeps every cell the callee kept: the caller's locals are
restored and only the result variable is written. -/
theorem assignCall_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (name : MlS) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (w : BitVec 64)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments = some values)
    (hlookup : lookupCodeHOLFinite t.code.lookup function values = some (body,callee,returnShape))
    (hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body).2.memory w = t.memory w) :
    (evaluateHOLFiniteState t (.call (some (some (kind,name),none)) function arguments)).2.memory w =
      t.memory w := by
  rw [evaluateHOLFiniteState_call,hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases run : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with
    | mk rb st =>
      rw [run] at hbody
      have hst : st.memory w = t.memory w := hbody
      have hkvar : ∀ (v : ValueHOL 64),
          (setKvarHOLFinite kind name v {st with locals := t.locals}).memory w = t.memory w := by
        intro v
        cases kind <;> (simp only [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite]; exact hst)
      cases rb with
      | none => exact hst
      | some rr =>
        cases rr with
        | «returned» value =>
          dsimp only
          split
          · split
            · exact hkvar value
            · exact hst
          · exact hst
        | _ =>
          dsimp only
          first
            | exact hst
            | (simp only [emptyLocalsHOLFinite]; exact hst)

#print axioms assignCall_window

/-- A continuing result-binding call is exactly the callee's returned word written into the result
variable, over the caller's locals. -/
theorem assignCall_none_facts {F : Type} (t : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (name : MlS) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (mid : PanSemStateFiniteExact 64 F)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments = some values)
    (hlookup : lookupCodeHOLFinite t.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState t (.call (some (some (kind,name),none)) function arguments) =
      (none, mid)) :
    ∃ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body = (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
        isValidValueHOLExact t.toExact kind name value = true ∧
        mid = setKvarHOLFinite kind name value {post with locals := t.locals} := by
  rw [evaluateHOLFiniteState_call,hargs] at run
  dsimp only at run
  rw [hlookup] at run
  dsimp only at run
  split at run
  · simp at run
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with
    | mk rb st =>
      rw [bodyRun] at run
      cases rb with
      | none => simp at run
      | some rr =>
        cases rr with
        | returned value =>
          dsimp only at run
          by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
          · rw [if_pos hshape] at run
            by_cases hvalid : isValidValueHOLExact t.toExact kind name value = true
            · rw [if_pos hvalid] at run
              exact ⟨value, st, rfl, hshape, hvalid, (Prod.mk.inj run).2.symm⟩
            · rw [if_neg hvalid] at run
              simp at run
          · rw [if_neg hshape] at run
            simp at run
        | _ => simp at run

#print axioms assignCall_none_facts

/-- Assigning a word to a local that already holds a word is valid. -/
theorem isValidValue_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (V X : BitVec 64)
    (h : s.locals.lookup name = some (.val (.word X))) :
    isValidValueHOLFinite s .local name (.val (.word V)) = true := by
  simp [isValidValueHOLFinite,lookupKvarHOLFinite,h,shapeOfHOLExact,shapeEqHOL]

#print axioms isValidValue_local_word

/-- The list-finishing tail of `encode_withdrawal_rlp` keeps every cell outside the buffer window:
the real `rlp_finish_list` writes only inside the `9 + payload` bytes at `buf`, and the payload is
the writer offset `K` less the nine-byte list-header slot. -/
theorem wdFinishTail_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B P w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K ≤ 64) (hK9 : 9 ≤ K)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t wdFinishTail).2.memory w = t.memory w := by
  rw [wdFinishTail]
  have argsEval : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.var .local (ofString "buf"), .var .local (ofString "p")] =
      some [.val (.word B), .val (.word P)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hb,hp]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact t.code.lookup
    (ofString "rlp_finish_list") [.val (.word B), .val (.word P)]
    (sourceFunctionBody Guest.guestFn_rlp_finish_list) _ .one
    (by rw [code]; exact rlpFinishList_exact_lookup B P)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hdC,heC⟩ := rlpFinishList_call_facts B P _ _ _ look'
  have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
      = some (.val (.word B)) := by
    rw [callEntryStateHOLFinite]; exact hdC
  have heE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "payload_end")
      = some (.val (.word P)) := by
    rw [callEntryStateHOLFinite]; exact heC
  have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hpayload : P - (B + 9#64) = BitVec.ofNat 64 (K - 9) := by
    rw [hP]; bv_omega
  have htoNat : (BitVec.ofNat 64 (K - 9)).toNat = K - 9 := by
    rw [BitVec.toNat_ofNat]; omega
  have hout : ¬ MWin B (9 + (P - (B + 9#64)).toNat) w := by
    rw [hpayload,htoNat]
    exact mwin_mono (by omega : 9 + (K - 9) ≤ 64) out
  have hsmall : (P - (B + 9#64)).toNat + 32 < 2 ^ 64 := by
    rw [hpayload,htoNat]; omega
  refine decCall_window t (ofString "total") .one (ofString "rlp_finish_list")
    [.var .local (ofString "buf"), .var .local (ofString "p")]
    (.return (.rstruct [.var .local (ofString "buf"), .var .local (ofString "total")]))
    w [.val (.word B), .val (.word P)]
    (sourceFunctionBody Guest.guestFn_rlp_finish_list) callee .one argsEval look ?_ ?_
  · exact rlpFinishList_window (callEntryStateHOLFinite t callee) B P (P - (B + 9#64)) w
      hout hsmall hdE heE rfl entryCode
  · intro value base run hsh1 hsh2 k
    rw [return_memory]
    have hbm : base.memory w = t.memory w := by
      have hbw := rlpFinishList_window (callEntryStateHOLFinite t callee) B P (P - (B + 9#64)) w
        hout hsmall hdE heE rfl entryCode
      rw [run] at hbw
      exact hbw
    simpa [setVarHOLFinite] using hbm

#print axioms wdFinishTail_window

/-- The `.one` shape check yields a word, reading the shape check from the parameter side. -/
theorem shapeWord_of_one_left {v : ValueHOL 64} (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with
    | word y => exact ⟨y,rfl⟩
  | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at h
  | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at h

#print axioms shapeWord_of_one_left

/-- If the lookup of `rlp_encode_word` succeeds at all, then its second argument is already a
word: the exact lookup's shape check enforces the `.one` parameter shape. -/
theorem rlpEncodeWord_second_word {P : BitVec 64} {A2 : ValueHOL 64} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {returnShape : ShapeHOL}
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_encode_word") [.val (.word P), A2] = some (body,callee,returnShape)) :
    ∃ Y : BitVec 64, A2 = .val (.word Y) := by
  by_cases hshape : shapeEqHOL .one (shapeOfHOLExact A2) = true
  · exact shapeWord_of_one_left hshape
  · exfalso
    have hnone : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_encode_word")
        [.val (.word P), A2] = none := by
      rw [lookupCodeHOLExact,originalRuntimeCode_rlp_encode_word_lookup]
      dsimp only
      rw [if_neg]
      intro hc
      have hall := hc.2.2
      simp only [List.zip_cons_cons,List.all_cons,List.all_nil,Bool.and_eq_true] at hall
      exact hshape hall.2.1
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
    split at found
    · cases found
    · rename_i raw
      rw [hnone] at raw
      cases raw

#print axioms rlpEncodeWord_second_word


/-- The amount writer, its offset advance and the list finish keep every cell outside the buffer
window.  The record word is left abstract: if it cannot be loaded the call simply fails, and if it is
loaded then the lookup's shape check makes it a word. -/
theorem wdCall36_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B P w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K + 9 ≤ 64) (hK9 : 9 ≤ K)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t (.seq wdCall36 wdCall36Tail)).2.memory w = t.memory w := by
  have hwd : wdCall36 = (.call (some ((some (.local,ofString "w")),none))
      (ofString "rlp_encode_word") [.var .local (ofString "p"), withdrawalWord36]) := rfl
  rw [hwd, evaluateHOLFiniteState_seq_line780]
  by_cases h2 : ∃ A2 : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord36 = some A2
  · obtain ⟨A2, h2⟩ := h2
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord36] = some [.val (.word P), A2] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp,h2]
    by_cases hlook : ∃ l, PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
        (ofString "rlp_encode_word") [.val (.word P), A2] = some l
    · obtain ⟨⟨body, callee, returnShape⟩, hlook⟩ := hlook
      have hlookO := hlook
      rw [code] at hlookO
      obtain ⟨Y, hY⟩ := rlpEncodeWord_second_word (P := P) hlookO
      have look2 : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
          (ofString "rlp_encode_word") [.val (.word P), .val (.word Y)] =
          some (body,callee,returnShape) := by
        rw [← hY]; exact hlookO
      obtain ⟨bodyEq,hshapeEq,hdC,hwC⟩ := rlpEncodeWord_call_facts P Y body callee returnShape look2
      have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
          = some (.val (.word P)) := by
        rw [callEntryStateHOLFinite]; exact hdC
      have hwE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "w")
          = some (.val (.word Y)) := by
        rw [callEntryStateHOLFinite]; exact hwC
      have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
        rw [callEntryStateHOLFinite]; exact code
      have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body).2.memory w
          = t.memory w := by
        rw [bodyEq]
        exact rlpEncodeWord_window (callEntryStateHOLFinite t callee) P Y w
          (by rw [hP]; exact mwin_narrow_shift out hK) hdE hwE entryCode
      cases callRun : evaluateHOLFiniteState t
          (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord36]) with
      | mk rc mid =>
        dsimp only
        cases rc with
        | some res =>
          have window := assignCall_window t .local (ofString "w") (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord36] [.val (.word P), A2]
            body callee returnShape w hargs hlook hbody
          rw [callRun] at window
          dsimp only at window
          exact window
        | none =>
          obtain ⟨value, post, bodyRun, hshape, hvalid, hmid⟩ :=
            assignCall_none_facts t .local (ofString "w") (ofString "rlp_encode_word")
              [.var .local (ofString "p"), withdrawalWord36] [.val (.word P), A2]
              body callee returnShape mid hargs hlook callRun
          obtain ⟨H, hval, hHle⟩ := rlpEncodeWord_returns_le_nine (callEntryStateHOLFinite t callee)
            Y entryCode value hwE (by rw [← bodyEq,bodyRun])
          have hpm : post.memory w = t.memory w := by
            rw [bodyRun] at hbody
            exact hbody
          rw [hmid, hval]
          simp only [setKvarHOLFinite]
          set sp := setVarHOLFinite (ofString "p") (.val (.word (P + H)))
            (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
          have hpL : (setVarHOLFinite (ofString "w") (.val (.word H))
              {post with locals := t.locals}).locals.lookup (ofString "p") = some (.val (.word P)) := by
            simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
              show ofString "w" ≠ ofString "p" by decide] using hp
          have hwL : (setVarHOLFinite (ofString "w") (.val (.word H))
              {post with locals := t.locals}).locals.lookup (ofString "w") = some (.val (.word H)) :=
            lookup_setVar_eq _ _ _
          have asg : evaluateHOLFiniteState
              (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
              wdAssign = (none, sp) := by
            simp only [sp,wdAssign,withdrawalOffset,evaluateHOLFiniteState_assign,setKvarHOLFinite]
            rw [show @evalHOLExact 64 F _
                (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).toExact
                (fun a => Classical.propDecidable
                  ((setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).memaddrs a))
                (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]) =
                some (.val (.word (P + H))) from by
              simp [evalHOLExact,evalListHOLExact,hpL,hwL,wordOpHOL,wordOp,valueIsWord,valueWord]]
            dsimp only
            rw [if_pos (isValidValue_local_word _ (ofString "p") (P + H) P hpL)]
          rw [wdCall36Tail, evaluateHOLFiniteState_seq_line780, asg]
          dsimp only
          have spmem : sp.memory w = t.memory w := by
            simp only [sp,setVarHOLFinite]
            exact hpm
          have hPloc : sp.locals.lookup (ofString "p") = some (.val (.word (P + H))) := by
            simp only [sp,setVarHOLFinite]
            exact lookup_setVar_eq _ _ _
          have hbloc : sp.locals.lookup (ofString "buf") = some (.val (.word B)) := by
            simp [sp,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hb,
              show ofString "p" ≠ ofString "buf" by decide,
              show ofString "w" ≠ ofString "buf" by decide]
          have postCode : post.code = t.code := by
            have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee)
              (sourceFunctionBody Guest.guestFn_rlp_encode_word)).1
            rw [← bodyEq,bodyRun] at met
            exact met
          have spcode : sp.code = originalRuntimeCode := by
            simp only [sp,setVarHOLFinite]
            exact postCode.trans code
          have hPn : P + H = B + BitVec.ofNat 64 (K + H.toNat) := by
            rw [hP]; bv_omega
          rw [wdFinishTail_window sp B (P + H) w (K + H.toNat) out hB hPn (by omega) (by omega)
            hbloc hPloc spcode]
          exact spmem
    · push_neg at hlook
      have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
          (ofString "rlp_encode_word") [.val (.word P), A2] = none := by
        cases h : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
            (ofString "rlp_encode_word") [.val (.word P), A2] with
        | none => rfl
        | some l => exact absurd h (hlook l)
      have hpair : evaluateHOLFiniteState t
          (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord36]) = (some .error, t) := by
        rw [evaluateHOLFiniteState_call,hargs]
        dsimp only
        rw [hnone]
      rw [hpair]
  · push_neg at h2
    have hnone : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord36 = none := by
      cases h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          withdrawalWord36 with
      | none => rfl
      | some v => exact absurd h (h2 v)
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord36] = none := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hnone]
    have hpair : evaluateHOLFiniteState t
        (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"), withdrawalWord36]) = (some .error, t) := by
      rw [evaluateHOLFiniteState_call,hargs]
    rw [hpair]

/-- The twenty-byte address writer, its offset advance and the amount writer keep every cell
outside the buffer window. -/
theorem wdCallBytes_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W P w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K ≤ 27) (hK9 : 9 ≤ K)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hwd : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t (.seq wdCallBytes wdCallBytesTail)).2.memory w = t.memory w := by
  have hwdE : wdCallBytes = (.call (some ((some (.local,ofString "w")),none))
      (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
       .const (20#64)]) := rfl
  rw [hwdE, evaluateHOLFiniteState_seq_line780]
  have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
       .const (20#64)] =
      some [.val (.word P), .val (.word (W + 16#64)), .val (.word (20#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp,hwd,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨callee, look⟩ := lookupCodeHOLFinite_of_exact t.code.lookup (ofString "rlp_encode_bytes")
    [.val (.word P), .val (.word (W + 16#64)), .val (.word (20#64))]
    (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) _ .one
    (by rw [code]; exact rlpEncodeBytes_exact_lookup P (W + 16#64) (20#64))
  have look' := look
  rw [code] at look'
  obtain ⟨hbodyEq,hshapeEq,hdC,hsC,hnC⟩ :=
    rlpEncodeBytes_call_facts P (W + 16#64) (20#64)
      (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) callee .one look'
  have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
      = some (.val (.word P)) := by
    rw [callEntryStateHOLFinite]; exact hdC
  have hsE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "src")
      = some (.val (.word (W + 16#64))) := by
    rw [callEntryStateHOLFinite]; exact hsC
  have hnE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "n")
      = some (.val (.word (20#64))) := by
    rw [callEntryStateHOLFinite]; exact hnC
  have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have h20 : (20#64 : BitVec 64).toNat = 20 := by decide
  have hsmall : (20#64 : BitVec 64).toNat + 32 < 2 ^ 64 := by omega
  have hout : ¬ MWin P (9 + (20#64 : BitVec 64).toNat) w := by
    have h29 : 9 + (20#64 : BitVec 64).toNat = 29 := by omega
    rw [h29, hP]
    exact mwin_narrow_shift out (by omega)
  have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
      (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)).2.memory w = t.memory w :=
    rlpEncodeBytes_window (callEntryStateHOLFinite t callee) P (W + 16#64) (20#64) w
      hout hsmall hdE hsE hnE entryCode
  cases callRun : evaluateHOLFiniteState t
      (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes")
        [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
         .const (20#64)]) with
  | mk rc mid =>
    dsimp only
    cases rc with
    | some res =>
      have window := assignCall_window t .local (ofString "w") (ofString "rlp_encode_bytes")
        [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
         .const (20#64)] [.val (.word P), .val (.word (W + 16#64)), .val (.word (20#64))]
        (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) callee .one w hargs look hbody
      rw [callRun] at window
      dsimp only at window
      exact window
    | none =>
      obtain ⟨value, post, bodyRun, hshape, hvalid, hmid⟩ :=
        assignCall_none_facts t .local (ofString "w") (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"), .op .add [.var .local (ofString "wd"), .const (16#64)],
           .const (20#64)] [.val (.word P), .val (.word (W + 16#64)), .val (.word (20#64))]
          (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) callee .one mid hargs look callRun
      obtain ⟨H, hval, hHle⟩ := rlpEncodeBytes_returns_le_one_add (callEntryStateHOLFinite t callee)
        P (W + 16#64) (20#64) entryCode value hdE hsE hnE (by omega) (by rw [bodyRun])
      have hH21 : H.toNat ≤ 21 := by omega
      have hpm : post.memory w = t.memory w := by
        rw [bodyRun] at hbody
        exact hbody
      rw [hmid, hval]
      simp only [setKvarHOLFinite]
      set sp := setVarHOLFinite (ofString "p") (.val (.word (P + H)))
        (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
      have hpL : (setVarHOLFinite (ofString "w") (.val (.word H))
          {post with locals := t.locals}).locals.lookup (ofString "p") = some (.val (.word P)) := by
        simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "w" ≠ ofString "p" by decide] using hp
      have hwL : (setVarHOLFinite (ofString "w") (.val (.word H))
          {post with locals := t.locals}).locals.lookup (ofString "w") = some (.val (.word H)) :=
        lookup_setVar_eq _ _ _
      have asg : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
          wdAssign = (none, sp) := by
        simp only [sp,wdAssign,withdrawalOffset,evaluateHOLFiniteState_assign,setKvarHOLFinite]
        rw [show @evalHOLExact 64 F _
            (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).toExact
            (fun a => Classical.propDecidable
              ((setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).memaddrs a))
            (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]) =
            some (.val (.word (P + H))) from by
          simp [evalHOLExact,evalListHOLExact,hpL,hwL,wordOpHOL,wordOp,valueIsWord,valueWord]]
        dsimp only
        rw [if_pos (isValidValue_local_word _ (ofString "p") (P + H) P hpL)]
      rw [wdCallBytesTail, evaluateHOLFiniteState_seq_line780, asg]
      dsimp only
      have spmem : sp.memory w = t.memory w := by
        simp only [sp,setVarHOLFinite]
        exact hpm
      have hPloc : sp.locals.lookup (ofString "p") = some (.val (.word (P + H))) := by
        simp only [sp,setVarHOLFinite]
        exact lookup_setVar_eq _ _ _
      have hbloc : sp.locals.lookup (ofString "buf") = some (.val (.word B)) := by
        simp [sp,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hb,
          show ofString "p" ≠ ofString "buf" by decide,
          show ofString "w" ≠ ofString "buf" by decide]
      have postCode : post.code = t.code := by
        have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee)
          (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)).1
        rw [bodyRun] at met
        exact met
      have spcode : sp.code = originalRuntimeCode := by
        simp only [sp,setVarHOLFinite]
        exact postCode.trans code
      have hPn : P + H = B + BitVec.ofNat 64 (K + H.toNat) := by
        rw [hP]; bv_omega
      rw [wdCall36_window sp B (P + H) w (K + H.toNat) out hB hPn (by omega) (by omega)
        hbloc hPloc spcode]
      exact spmem

#print axioms wdCall36_window

#print axioms wdCallBytes_window

theorem wdCall8_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W P w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K ≤ 18) (hK9 : 9 ≤ K)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hwdloc : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t (.seq wdCall8 wdCall8Tail)).2.memory w = t.memory w := by
  have hwd : wdCall8 = (.call (some ((some (.local,ofString "w")),none))
      (ofString "rlp_encode_word") [.var .local (ofString "p"), withdrawalWord8]) := rfl
  rw [hwd, evaluateHOLFiniteState_seq_line780]
  by_cases h2 : ∃ A2 : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord8 = some A2
  · obtain ⟨A2, h2⟩ := h2
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord8] = some [.val (.word P), A2] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp,h2]
    by_cases hlook : ∃ l, PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
        (ofString "rlp_encode_word") [.val (.word P), A2] = some l
    · obtain ⟨⟨body, callee, returnShape⟩, hlook⟩ := hlook
      have hlookO := hlook
      rw [code] at hlookO
      obtain ⟨Y, hY⟩ := rlpEncodeWord_second_word (P := P) hlookO
      have look2 : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
          (ofString "rlp_encode_word") [.val (.word P), .val (.word Y)] =
          some (body,callee,returnShape) := by
        rw [← hY]; exact hlookO
      obtain ⟨bodyEq,hshapeEq,hdC,hwC⟩ := rlpEncodeWord_call_facts P Y body callee returnShape look2
      have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
          = some (.val (.word P)) := by
        rw [callEntryStateHOLFinite]; exact hdC
      have hwE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "w")
          = some (.val (.word Y)) := by
        rw [callEntryStateHOLFinite]; exact hwC
      have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
        rw [callEntryStateHOLFinite]; exact code
      have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body).2.memory w
          = t.memory w := by
        rw [bodyEq]
        exact rlpEncodeWord_window (callEntryStateHOLFinite t callee) P Y w
          (by rw [hP]; exact mwin_narrow_shift out (by omega)) hdE hwE entryCode
      cases callRun : evaluateHOLFiniteState t
          (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord8]) with
      | mk rc mid =>
        dsimp only
        cases rc with
        | some res =>
          have window := assignCall_window t .local (ofString "w") (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord8] [.val (.word P), A2]
            body callee returnShape w hargs hlook hbody
          rw [callRun] at window
          dsimp only at window
          exact window
        | none =>
          obtain ⟨value, post, bodyRun, hshape, hvalid, hmid⟩ :=
            assignCall_none_facts t .local (ofString "w") (ofString "rlp_encode_word")
              [.var .local (ofString "p"), withdrawalWord8] [.val (.word P), A2]
              body callee returnShape mid hargs hlook callRun
          obtain ⟨H, hval, hHle⟩ := rlpEncodeWord_returns_le_nine (callEntryStateHOLFinite t callee)
            Y entryCode value hwE (by rw [← bodyEq,bodyRun])
          have hpm : post.memory w = t.memory w := by
            rw [bodyRun] at hbody
            exact hbody
          rw [hmid, hval]
          simp only [setKvarHOLFinite]
          set sp := setVarHOLFinite (ofString "p") (.val (.word (P + H)))
            (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
          have hpL : (setVarHOLFinite (ofString "w") (.val (.word H))
              {post with locals := t.locals}).locals.lookup (ofString "p") = some (.val (.word P)) := by
            simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
              show ofString "w" ≠ ofString "p" by decide] using hp
          have hwL : (setVarHOLFinite (ofString "w") (.val (.word H))
              {post with locals := t.locals}).locals.lookup (ofString "w") = some (.val (.word H)) :=
            lookup_setVar_eq _ _ _
          have asg : evaluateHOLFiniteState
              (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals})
              wdAssign = (none, sp) := by
            simp only [sp,wdAssign,withdrawalOffset,evaluateHOLFiniteState_assign,setKvarHOLFinite]
            rw [show @evalHOLExact 64 F _
                (setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).toExact
                (fun a => Classical.propDecidable
                  ((setVarHOLFinite (ofString "w") (.val (.word H)) {post with locals := t.locals}).memaddrs a))
                (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]) =
                some (.val (.word (P + H))) from by
              simp [evalHOLExact,evalListHOLExact,hpL,hwL,wordOpHOL,wordOp,valueIsWord,valueWord]]
            dsimp only
            rw [if_pos (isValidValue_local_word _ (ofString "p") (P + H) P hpL)]
          rw [wdCall8Tail, evaluateHOLFiniteState_seq_line780, asg]
          dsimp only
          have spmem : sp.memory w = t.memory w := by
            simp only [sp,setVarHOLFinite]
            exact hpm
          have hPloc : sp.locals.lookup (ofString "p") = some (.val (.word (P + H))) := by
            simp only [sp,setVarHOLFinite]
            exact lookup_setVar_eq _ _ _
          have hbloc : sp.locals.lookup (ofString "buf") = some (.val (.word B)) := by
            simp [sp,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hb,
              show ofString "p" ≠ ofString "buf" by decide,
              show ofString "w" ≠ ofString "buf" by decide]
          have postCode : post.code = t.code := by
            have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee)
              (sourceFunctionBody Guest.guestFn_rlp_encode_word)).1
            rw [← bodyEq,bodyRun] at met
            exact met
          have spcode : sp.code = originalRuntimeCode := by
            simp only [sp,setVarHOLFinite]
            exact postCode.trans code
          have hwn : sp.locals.lookup (ofString "wd") = some (.val (.word W)) := by
            simpa [sp,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
              show ofString "p" ≠ ofString "wd" by decide,
              show ofString "w" ≠ ofString "wd" by decide] using hwdloc
          have hPn : P + H = B + BitVec.ofNat 64 (K + H.toNat) := by
            rw [hP]; bv_omega
          rw [wdCallBytes_window sp B W (P + H) w (K + H.toNat) out hB hPn (by omega) (by omega)
            hbloc hPloc hwn spcode]
          exact spmem
    · push_neg at hlook
      have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
          (ofString "rlp_encode_word") [.val (.word P), A2] = none := by
        cases h : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
            (ofString "rlp_encode_word") [.val (.word P), A2] with
        | none => rfl
        | some l => exact absurd h (hlook l)
      have hpair : evaluateHOLFiniteState t
          (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"), withdrawalWord8]) = (some .error, t) := by
        rw [evaluateHOLFiniteState_call,hargs]
        dsimp only
        rw [hnone]
      rw [hpair]
  · push_neg at h2
    have hnone : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord8 = none := by
      cases h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          withdrawalWord8 with
      | none => rfl
      | some v => exact absurd h (h2 v)
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord8] = none := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hnone]
    have hpair : evaluateHOLFiniteState t
        (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"), withdrawalWord8]) = (some .error, t) := by
      rw [evaluateHOLFiniteState_call,hargs]
    rw [hpair]
#print axioms wdCall8_window


/-- After the first record word is bound, the offset advance followed by the second and address
writers keeps every cell outside the buffer window. -/
theorem wdAssign8_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W P H w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K ≤ 9) (hK9 : 9 ≤ K) (hH : H.toNat ≤ 9)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hwdloc : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word H)) t)
      (.seq wdAssign (.seq wdCall8 wdCall8Tail))).2.memory w = t.memory w := by
  set t' := setVarHOLFinite (ofString "w") (.val (.word H)) t with ht'
  have hpL : t'.locals.lookup (ofString "p") = some (.val (.word P)) := by
    simp only [ht',setVarHOLFinite]
    exact lookup_setVar_ne _ (ofString "w") (ofString "p") _ _ (by decide) (by simpa using hp)
  have hwL : t'.locals.lookup (ofString "w") = some (.val (.word H)) := by
    simp only [ht',setVarHOLFinite]
    exact lookup_setVar_eq _ _ _
  have asg : evaluateHOLFiniteState t' wdAssign = (none, setVarHOLFinite (ofString "p")
      (.val (.word (P + H))) t') := by
    simp only [ht',wdAssign,withdrawalOffset,evaluateHOLFiniteState_assign,setKvarHOLFinite]
    rw [show @evalHOLExact 64 F _ t'.toExact
        (fun a => Classical.propDecidable (t'.memaddrs a))
        (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]) =
        some (.val (.word (P + H))) from by
      simp [evalHOLExact,evalListHOLExact,hpL,hwL,wordOpHOL,wordOp,valueIsWord,valueWord]]
    dsimp only
    rw [if_pos (isValidValue_local_word _ (ofString "p") (P + H) P hpL)]
  set sp := setVarHOLFinite (ofString "p") (.val (.word (P + H))) t' with hsp
  rw [evaluateHOLFiniteState_seq_line780, asg]
  dsimp only
  have hbloc : sp.locals.lookup (ofString "buf") = some (.val (.word B)) := by
    simp [hsp,ht',setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hb,
      show ofString "p" ≠ ofString "buf" by decide,
      show ofString "w" ≠ ofString "buf" by decide]
  have hPloc : sp.locals.lookup (ofString "p") = some (.val (.word (P + H))) := by
    simp only [hsp,setVarHOLFinite]
    exact lookup_setVar_eq _ _ _
  have hwn : sp.locals.lookup (ofString "wd") = some (.val (.word W)) := by
    simp [hsp,ht',setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hwdloc,
      show ofString "p" ≠ ofString "wd" by decide,
      show ofString "w" ≠ ofString "wd" by decide]
  have spmem : sp.memory w = t.memory w := by
    simp only [hsp,ht',setVarHOLFinite]
  have spcode : sp.code = originalRuntimeCode := by
    simp only [hsp,ht',setVarHOLFinite]
    exact code
  have hPn : P + H = B + BitVec.ofNat 64 (K + H.toNat) := by
    rw [hP]; bv_omega
  rw [wdCall8_window sp B W (P + H) w (K + H.toNat) out hB hPn (by omega) (by omega)
    hbloc hPloc hwn spcode]
  exact spmem

#print axioms wdAssign8_window

/-- The first record word written through the destructuring call, and the whole remaining writer
chain, keep every cell outside the buffer window. -/
theorem wdCall0_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W P w : BitVec 64) (K : Nat)
    (out : ¬ MWin B 64 w)
    (hB : B.toNat + 64 < 2 ^ 64)
    (hP : P = B + BitVec.ofNat 64 K)
    (hK : K ≤ 9) (hK9 : 9 ≤ K)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hwdloc : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t wdCall0).2.memory w = t.memory w := by
  have hdc : wdCall0 = (.decCall (ofString "w") .one (ofString "rlp_encode_word")
      [.var .local (ofString "p"), withdrawalWord0] wdCall0Tail) := rfl
  rw [hdc]
  by_cases h2 : ∃ A2 : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord0 = some A2
  · obtain ⟨A2, h2⟩ := h2
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord0] = some [.val (.word P), A2] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp,h2]
    by_cases hlook : ∃ l, PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
        (ofString "rlp_encode_word") [.val (.word P), A2] = some l
    · obtain ⟨⟨body, callee, returnShape⟩, hlook⟩ := hlook
      have hlookO := hlook
      rw [code] at hlookO
      obtain ⟨Y, hY⟩ := rlpEncodeWord_second_word (P := P) hlookO
      have look2 : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
          (ofString "rlp_encode_word") [.val (.word P), .val (.word Y)] =
          some (body,callee,returnShape) := by
        rw [← hY]; exact hlookO
      obtain ⟨bodyEq,hshapeEq,hdC,hwC⟩ := rlpEncodeWord_call_facts P Y body callee returnShape look2
      have hdE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "dst")
          = some (.val (.word P)) := by
        rw [callEntryStateHOLFinite]; exact hdC
      have hwE : (callEntryStateHOLFinite t callee).locals.lookup (ofString "w")
          = some (.val (.word Y)) := by
        rw [callEntryStateHOLFinite]; exact hwC
      have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
        rw [callEntryStateHOLFinite]; exact code
      have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body).2.memory w
          = t.memory w := by
        rw [bodyEq]
        exact rlpEncodeWord_window (callEntryStateHOLFinite t callee) P Y w
          (by rw [hP]; exact mwin_narrow_shift out (by omega)) hdE hwE entryCode
      refine decCall_window t (ofString "w") .one (ofString "rlp_encode_word")
        [.var .local (ofString "p"), withdrawalWord0] wdCall0Tail w [.val (.word P), A2]
        body callee returnShape hargs hlook hbody ?_
      intro value base bodyRun hshapeOK hshapeR k
      obtain ⟨H, hval, hHle⟩ := rlpEncodeWord_returns_le_nine (callEntryStateHOLFinite t callee)
        Y entryCode value hwE (by rw [← bodyEq,bodyRun])
      have hbase : base.memory w = t.memory w := by
        rw [bodyRun] at hbody
        exact hbody
      have basecode : base.code = originalRuntimeCode := by
        have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee)
          (sourceFunctionBody Guest.guestFn_rlp_encode_word)).1
        rw [← bodyEq,bodyRun] at met
        exact met.trans entryCode
      rw [hval, wdCall0Tail]
      have key := wdAssign8_window (t := {base with clock := k, locals := t.locals}) B W P H w K
        out hB hP hK hK9 hHle (by simpa using hb) (by simpa using hp) (by simpa using hwdloc)
        (by simpa using basecode)
      have hmem : ({base with clock := k, locals := t.locals} : PanSemStateFiniteExact 64 F).memory w
          = t.memory w := hbase
      rw [key]
      exact hmem
    · push_neg at hlook
      have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
          (ofString "rlp_encode_word") [.val (.word P), A2] = none := by
        cases h : PanSemStateFiniteExact.lookupCodeHOLFinite t.code.lookup
            (ofString "rlp_encode_word") [.val (.word P), A2] with
        | none => rfl
        | some l => exact absurd h (hlook l)
      rw [evaluateHOLFiniteState_decCall_total,hargs]
      dsimp only
      rw [hnone]
  · push_neg at h2
    have hnone : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        withdrawalWord0 = none := by
      cases h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          withdrawalWord0 with
      | none => rfl
      | some v => exact absurd h (h2 v)
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "p"), withdrawalWord0] = none := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hnone]
    rw [evaluateHOLFiniteState_decCall_total,hargs]

#print axioms wdCall0_window

/-- Declaring the writer cursor at `buf + 9` and running the whole writer chain keeps every cell
outside the buffer window. -/
theorem wdDecP_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W w : BitVec 64)
    (out : ¬ MWin B 64 w) (hB : B.toNat + 64 < 2 ^ 64)
    (hb : t.locals.lookup (ofString "buf") = some (.val (.word B)))
    (hwdloc : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t (.dec (ofString "p") .one
      (.op .add [.var .local (ofString "buf"), .const (9#64)]) wdCall0)).2.memory w = t.memory w := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [show @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .local (ofString "buf"), .const (9#64)]) =
      some (.val (.word (B + 9#64))) from by
    simp [evalHOLExact,evalListHOLExact,hb,wordOpHOL,wordOp,valueIsWord,valueWord]]
  dsimp only
  rw [if_pos (by simp [shapeOfHOLExact,shapeEqHOL])]
  set bs := setVarHOLFinite (ofString "p") (.val (.word (B + 9#64))) t with hbs
  have hbp : bs.locals.lookup (ofString "buf") = some (.val (.word B)) := by
    simp [hbs,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hb,
      show ofString "p" ≠ ofString "buf" by decide]
  have hpp : bs.locals.lookup (ofString "p") = some (.val (.word (B + 9#64))) := by
    simp [hbs,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have hwp : bs.locals.lookup (ofString "wd") = some (.val (.word W)) := by
    simp [hbs,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hwdloc,
      show ofString "p" ≠ ofString "wd" by decide]
  have bscode : bs.code = originalRuntimeCode := by
    simp only [hbs,setVarHOLFinite]
    exact code
  have key := wdCall0_window bs B W (B + 9#64) w 9 out hB rfl (by decide) (by decide)
    hbp hpp hwp bscode
  simpa [hbs,setVarHOLFinite] using key

#print axioms wdDecP_window

/-- Writing one withdrawal record touches no cell outside the freshly allocated sixty-four byte
buffer starting at the heap pointer. -/
theorem rlpEncodeWithdrawal_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (B W w : BitVec 64)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (hwd : t.locals.lookup (ofString "wd") = some (.val (.word W)))
    (out : ¬ MWin B 64 w) (hB : B.toNat + 64 < 2 ^ 64)
    (code : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)).2.memory w
      = t.memory w := by
  rw [source_rlpEncodeWithdrawal_body, rlpEncodeWithdrawal_eq]
  set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update ((ofString "n"), .val (.word (64#64))) with hcallee
  have args : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.const (64#64)] = some [.val (.word (64#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have installed : t.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup t.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) (64#64) installed
  refine decCall_window t (ofString "buf") .one (ofString "alloc") [.const (64#64)] wdDecP w
    [.val (.word (64#64))] (sourceFunctionBody Guest.guestFn_alloc) callee .one args lookup ?_ ?_
  · rw [alloc_memKeep (callEntryStateHOLFinite t callee)
      (by rw [callEntryStateHOLFinite]; exact code)]
    rfl
  · intro value base bodyRun hshapeOK hshapeR k
    have entryHeap : (callEntryStateHOLFinite t callee).globals.lookup (ofString "heap_ptr")
        = some (.val (.word B)) := by
      rw [callEntryStateHOLFinite]; exact heap
    have entrySize : (callEntryStateHOLFinite t callee).locals.lookup (ofString "n")
        = some (.val (.word (64#64))) := by
      simp [hcallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have entryCode : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := by
      rw [callEntryStateHOLFinite]; exact code
    obtain ⟨-, -, hval, -, -, -, -, -⟩ := alloc_body_returned (callEntryStateHOLFinite t callee)
      base B (64#64) entryCode entryHeap entrySize value bodyRun
    have basemem : base.memory w = t.memory w := by
      have kept := alloc_memKeep (callEntryStateHOLFinite t callee) entryCode
      rw [bodyRun] at kept
      change base.memory = (callEntryStateHOLFinite t callee).memory at kept
      rw [kept]
      rfl
    have basecode : base.code = originalRuntimeCode := by
      have met := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee)
        (sourceFunctionBody Guest.guestFn_alloc)).1
      rw [bodyRun] at met
      exact met.trans entryCode
    rw [hval]
    set st := setVarHOLFinite (ofString "buf") (.val (.word B))
      {base with clock := k, locals := t.locals} with hst
    have hb : st.locals.lookup (ofString "buf") = some (.val (.word B)) := by
      simp only [hst,setVarHOLFinite]
      exact lookup_setVar_eq _ _ _
    have hwdl : st.locals.lookup (ofString "wd") = some (.val (.word W)) := by
      simp [hst,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hwd,
        show ofString "buf" ≠ ofString "wd" by decide]
    have stcode : st.code = originalRuntimeCode := by
      simp only [hst,setVarHOLFinite]
      exact basecode
    have key := wdDecP_window st B W w out hB hb hwdl stcode
    have goalEq : st.memory w = t.memory w := by
      simpa [hst,setVarHOLFinite] using basemem
    rw [show wdDecP = (.dec (ofString "p") .one
      (.op .add [.var .local (ofString "buf"), .const (9#64)]) wdCall0) from rfl]
    rw [key]
    exact goalEq

#print axioms rlpEncodeWithdrawal_window

end InitECandidate.Runtime
