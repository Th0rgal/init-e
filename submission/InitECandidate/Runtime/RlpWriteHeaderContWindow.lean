import InitECandidate.Runtime.RlpWriteHeaderWindow
import InitECandidate.Runtime.RlpWindowCalls
import InitECandidate.Runtime.RlpCalleeValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- **The long-header continuation shared by the RLP writers.**  It stores the length byte at `dst`,
writes the big endian byte count at `dst + 1` through the actual `rlp_put_be`, then returns the total
length.  Given the prefix length `ll` fits in at most eight bytes, the value expression is arbitrary
(the frame argument never evaluates it) and the counted word is supplied by the caller through the
argument evaluation, it writes only inside the nine-byte window at `dst`. -/
theorem rlpLongTail_window {F : Type} (cs : PanSemStateFiniteExact 64 F)
    (D L V w : BitVec 64) (out : ¬ MWin D 9 w)
    (value vExp : ExpHOL 64)
    (hd : cs.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hl : cs.locals.lookup (ofString "ll") = some (.val (.word L)))
    (hargs : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F'), t.locals = cs.locals →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "dst"), .const (1#64)],
         vExp, .var .local (ofString "ll")] =
        some [.val (.word (D + 1#64)),.val (.word V),.val (.word L)])
    (hL : L.toNat ≤ 8)
    (code : cs.code = originalRuntimeCode) :
    (evaluateHOLFiniteState cs (.seq (.storeByte (.var .local (ofString "dst")) value)
      (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           vExp, .var .local (ofString "ll")])
        (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))).2.memory w =
      cs.memory w := by
  have dstEval : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
      (.var .local (ofString "dst")) = some (.val (.word D)) := by
    simp [evalHOLExact,hd]
  have sep : w ≠ panByteAlignHOL D := by
    intro h
    refine out ⟨0,by decide,Or.inr ?_⟩
    rw [show (D + BitVec.ofNat 64 0) = D from by simp]
    exact h
  have store := evaluate_storeByte_memory_frame cs (.var .local (ofString "dst")) value D w dstEval sep
  have control := evaluate_storeByte_control_frame cs (.var .local (ofString "dst")) value
  rw [evaluateHOLFiniteState_seq_line780]
  cases storeRun : evaluateHOLFiniteState cs (.storeByte (.var .local (ofString "dst")) value) with
  | mk sr sPost =>
    rw [storeRun] at store control
    obtain ⟨_,_,localsEq,_,codeEq,_,_⟩ := control
    cases sr with
    | none =>
      dsimp only
      have hd' : sPost.locals.lookup (ofString "dst") = some (.val (.word D)) := by
        rw [show sPost.locals = cs.locals from localsEq]; exact hd
      have hl' : sPost.locals.lookup (ofString "ll") = some (.val (.word L)) := by
        rw [show sPost.locals = cs.locals from localsEq]; exact hl
      have code' : sPost.code = originalRuntimeCode := by
        rw [show sPost.code = cs.code from codeEq]; exact code
      have inner : (evaluateHOLFiniteState sPost (.seq (.call (some (none,none))
          (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           vExp, .var .local (ofString "ll")])
          (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))).2.memory w =
          sPost.memory w := by
        refine window_seq sPost w ?_ ?_
        · have argsEval := hargs (t := sPost) (show sPost.locals = cs.locals from localsEq)
          obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact sPost.code.lookup
            (ofString "rlp_put_be")
            [.val (.word (D + 1#64)),.val (.word V),.val (.word L)]
            (sourceFunctionBody Guest.guestFn_rlp_put_be) _ .one
            (by rw [code']; exact rlpPutBe_exact_lookup _ _ _)
          have look' := look
          rw [code'] at look'
          obtain ⟨_,_,hdst,_,hnl⟩ := rlpPutBe_call_facts (D + 1#64) V L
            (sourceFunctionBody Guest.guestFn_rlp_put_be) callee .one look'
          exact discardCall_window sPost (ofString "rlp_put_be") _ _ _ callee .one w argsEval look
            (rlpPutBe_window (D + 1#64) L w (fun h => out (mwin_shift_one h hL))
              (callEntryStateHOLFinite sPost callee) hdst hnl)
        · intro u hu
          exact (return_memory u (.op .add [.const (1#64), .var .local (ofString "ll")]) w).trans hu
      exact inner.trans store
    | some res =>
      dsimp only
      cases res <;> first | exact store | (dsimp only; exact store)

#print axioms rlpLongTail_window

end InitECandidate.Runtime
