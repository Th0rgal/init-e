import InitECandidate.Runtime.RlpEncodeWithdrawal
import InitECandidate.Runtime.RlpEncodeBytesTight
import InitECandidate.Runtime.RlpWindowShiftGeneral
import InitECandidate.Runtime.RlpWindowCalls
import InitECandidate.Runtime.RlpEncodeWordWindow
import InitECandidate.Runtime.RlpEncodeBytesWindow
import InitECandidate.Runtime.RlpPutBeWindow
import InitECandidate.Runtime.RlpCalleeValues
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

end InitECandidate.Runtime
