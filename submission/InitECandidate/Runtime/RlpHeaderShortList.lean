import InitECandidate.Runtime.RlpItemLongFullContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderAfterByte : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_item_header with
  | .seq _ (.dec _ _ _ body) => body
  | _ => .skip

def rlpHeaderAfterSingle : ProgHOL 64 :=
  match rlpHeaderAfterByte with | .seq _ body => body | _ => .skip

def rlpHeaderAfterShortString : ProgHOL 64 :=
  match rlpHeaderAfterSingle with | .seq _ body => body | _ => .skip

def rlpHeaderAfterLongString : ProgHOL 64 :=
  match rlpHeaderAfterShortString with | .seq _ body => body | _ => .skip

def rlpHeaderShortList : ProgHOL 64 :=
  match rlpHeaderAfterLongString with | .seq (.ite _ body _) _ => body | _ => .skip

def rlpHeaderShortListBody : ProgHOL 64 :=
  match rlpHeaderShortList with | .dec _ _ _ body => body | _ => .skip

def rlpHeaderShortListReturn : ProgHOL 64 :=
  .return (.rstruct [.const 1,.var .local (ofString "n"),.const 1])

def rlpHeaderShortListValue (length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 1),.val (.word length),.val (.word 1)]

theorem source_rlpHeader_short_list_body : rlpHeaderShortListBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip) rlpHeaderShortListReturn := by
  simp only [rlpHeaderShortListBody,rlpHeaderShortList,rlpHeaderAfterLongString,rlpHeaderAfterShortString,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,rlpHeaderShortListReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpHeader_short_list : rlpHeaderShortList =
    .dec (ofString "n") .one (.op .sub [.var .local (ofString "b"),.const 192]) rlpHeaderShortListBody := by
  simp only [rlpHeaderShortListBody,rlpHeaderShortList,rlpHeaderAfterLongString,rlpHeaderAfterShortString,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original short-list header body validates availability and returns
its exact header/payload/list fields within one source tick. -/
theorem evaluate_rlpHeader_short_list_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderShortListBody = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpHeaderShortListValue length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpHeaderShortListReturn =
      (some (.returned (rlpHeaderShortListValue length)),emptyLocalsHOLFinite state) := by
    simp [rlpHeaderShortListReturn,rlpHeaderShortListValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      lengthLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,noReturn,memory,globals⟩ :=
    evaluate_rlp_error_check state
      (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) 3 code ticks
  rw [source_rlpHeader_short_list_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    dsimp only
    rw [returned]
    refine ⟨_,_,rfl,by change state.clock ≤ state.clock + 1; omega,by rfl,by simp,by simp,?_,rfl,rfl⟩
    intro value equal
    simpa using equal.symm
  | some stopped =>
    exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,by simp,
      (by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

/-- Returning past the real short-list header size check proves that its payload
fits in the supplied bytes and that the consumed length strictly advances. -/
theorem rlpHeader_short_list_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload total : BitVec 64) (value : ValueHOL 64)
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (small : payload.toNat ≤ 55)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortListBody = (some (.returned value),post)) :
    payload.toNat < total.toNat ∧ 0 < (1 + payload).toNat ∧ (1 + payload).toNat ≤ total.toNat := by
  have fits : payload.toNat ≤ (total - 1).toNat := by
    by_contra bad
    have less : (total - 1).toNat < payload.toNat := by omega
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) =
        some (.val (.word 1)) := by
      simp [evalHOLExact,evalListHOLExact,totalLocal,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
      simpa [BitVec.toNat_sub,Nat.add_comm] using less
    rw [source_rlpHeader_short_list_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have bound := evaluate_rlpFail_call_terminal state (.const 3) 3 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result output =>
      rw [called] at bound noReturn run
      dsimp only at bound noReturn run
      cases result with
      | none => exact False.elim (bound rfl)
      | some stopped =>
        exact False.elim (noReturn (Prod.mk.inj run).1)
  have positive : 0 < total.toNat := by
    by_contra h
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ total.toNat; omega)] at fits
  have consumed : (1 + payload).toNat = 1 + payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1 + payload.toNat < 2^64; omega)]
    rfl
  rw [consumed]
  change payload.toNat ≤ total.toNat - 1 at fits
  omega

/-- The original payload-length declaration preserves short-list header progress. -/
theorem rlpHeader_short_list_scoped_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortList = (some (.returned value),post)) :
    (header - 192).toNat < total.toNat ∧ 0 < (1 + (header - 192)).toNat ∧
      (1 + (header - 192)).toNat ≤ total.toNat := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_short_list] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "n")
    (.op .sub [.var .local (ofString "b"),.const 192]) (header - 192) rlpHeaderShortListBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 192))) state
  have atPayload : entered.locals.lookup (ofString "n") = some (.val (.word (header - 192))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have small : (header - 192).toNat ≤ 55 := by
    rw [BitVec.toNat_sub_of_le (show (192 : BitVec 64) ≤ header from BitVec.le_def.mpr lower)]
    change header.toNat - 192 ≤ 55
    omega
  exact rlpHeader_short_list_return_progress entered output (header - 192) total value
    atPayload atTotal nonzero small code bodyRun

#print axioms rlpHeader_short_list_scoped_progress
#print axioms rlpHeader_short_list_return_progress
#print axioms evaluate_rlpHeader_short_list_body
end InitECandidate.Runtime
