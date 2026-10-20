import InitECandidate.Runtime.RlpEncodeBytesReturns
import InitECandidate.Runtime.RlpFinishList
import InitECandidate.Runtime.OriginalRlpWriterCode
import InitECandidate.Proofs.FrontendStages.Declarations.Agreement877
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendStages.Declarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-- The first eight bytes of the withdrawal record as a word: bytes 0-3 little endian, then bytes
4-7 shifted up by 32. -/
def withdrawalWord0 : ExpHOL 64 :=
  .op .or [.loadByte (.var .local (ofString "wd")),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (1#64)])) (.const (8#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (2#64)])) (.const (16#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (3#64)])) (.const (24#64)),
    .shift .lsl (.op .or [.loadByte (.op .add [.var .local (ofString "wd"), .const (4#64)]),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (4#64), .const (1#64)])) (.const (8#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (4#64), .const (2#64)])) (.const (16#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (4#64), .const (3#64)])) (.const (24#64))]) (.const (32#64))]

/-- The second eight bytes of the withdrawal record as a word, read from `wd + 8`. -/
def withdrawalWord8 : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64)]),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (1#64)])) (.const (8#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (2#64)])) (.const (16#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (3#64)])) (.const (24#64)),
    .shift .lsl (.op .or [.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (4#64)]),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (4#64), .const (1#64)])) (.const (8#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (4#64), .const (2#64)])) (.const (16#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (8#64), .const (4#64), .const (3#64)])) (.const (24#64))]) (.const (32#64))]

/-- The amount word of the withdrawal record, read from `wd + 36`. -/
def withdrawalWord36 : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64)]),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (1#64)])) (.const (8#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (2#64)])) (.const (16#64)),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (3#64)])) (.const (24#64)),
    .shift .lsl (.op .or [.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (4#64)]),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (4#64), .const (1#64)])) (.const (8#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (4#64), .const (2#64)])) (.const (16#64)),
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "wd"), .const (36#64), .const (4#64), .const (3#64)])) (.const (24#64))]) (.const (32#64))]

/-- The running writer offset of `encode_withdrawal_rlp`. -/
def withdrawalOffset : ExpHOL 64 :=
  .op .add [.var .local (ofString "p"), .var .local (ofString "w")]

/-- The body of the actual `encode_withdrawal_rlp`: allocate the 64-byte buffer, point the writer
cursor at `buf + 9` (leaving room for the list header), serialize the four record fields with the
real RLP writers, and finish the list. -/
def rlpEncodeWithdrawal : ProgHOL 64 :=
  .decCall (ofString "buf") .one (ofString "alloc") [(.const (64#64))]
    (.dec (ofString "p") .one (.op .add [.var .local (ofString "buf"), .const (9#64)])
      (.decCall (ofString "w") .one (ofString "rlp_encode_word")
        [.var .local (ofString "p"), withdrawalWord0]
        (.seq (.assign .local (ofString "p") withdrawalOffset)
          (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
              [.var .local (ofString "p"), withdrawalWord8])
            (.seq (.assign .local (ofString "p") withdrawalOffset)
              (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"),
                   .op .add [.var .local (ofString "wd"), .const (16#64)], .const (20#64)])
                (.seq (.assign .local (ofString "p") withdrawalOffset)
                  (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word")
                      [.var .local (ofString "p"), withdrawalWord36])
                    (.seq (.assign .local (ofString "p") withdrawalOffset)
                      (.decCall (ofString "total") .one (ofString "rlp_finish_list")
                        [.var .local (ofString "buf"), .var .local (ofString "p")]
                        (.return (.rstruct [.var .local (ofString "buf"),
                          .var .local (ofString "total")]))))))))))))

/-- The body equation of the actual `encode_withdrawal_rlp`. -/
theorem source_rlpEncodeWithdrawal_body :
    sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp = rlpEncodeWithdrawal := by
  rw [rlpEncodeWithdrawal,withdrawalWord0,withdrawalWord8,withdrawalWord36,withdrawalOffset]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpEncodeWithdrawal_body


/-- The installed code entry of `encode_withdrawal_rlp` with its one word parameter. -/
theorem originalRuntimeCode_encode_withdrawal_rlp_lookup :
    originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd",.one)],
        sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp,.comb [.one,.one]) := by
  refine originalRuntimeCode_lookup_split (ofString "encode_withdrawal_rlp")
    (originals.take 877) original877 (originals.drop 878)
    [(ofString "wd",.one)]
    (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) (.comb [.one,.one]) ?_ ?_ ?_
  · kernel_rfl
  · rw [original877_eq]
    simp only [Guest.guestFn_encode_withdrawal_rlp,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_encode_withdrawal_rlp_lookup

/-- The exact code lookup of `encode_withdrawal_rlp` binds its one word parameter. -/
theorem rlpEncodeWithdrawal_exact_lookup (W : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp")
      [.val (.word W)] =
      some (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp,
        (fun x => if x = ofString "wd" then some (.val (.word W)) else none), .comb [.one,.one]) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_encode_withdrawal_rlp_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpEncodeWithdrawal_exact_lookup

/-- A successful finite lookup of the installed `encode_withdrawal_rlp` on one word argument has
the installed body, a two-word return shape, and reads the argument back under its name. -/
theorem rlpEncodeWithdrawal_call_facts (W : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "encode_withdrawal_rlp") [.val (.word W)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp ∧
      returnShape = .comb [.one,.one] ∧
      callee.lookup (ofString "wd") = some (.val (.word W)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpEncodeWithdrawal_exact_lookup W] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp +decide

#print axioms rlpEncodeWithdrawal_call_facts

end InitECandidate.Runtime
