import InitECandidate.Runtime.PayloadHeaderTailSources
import InitECandidate.Runtime.RlpWithdrawalWriter
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The loop condition `i < nwd` of statement 46. -/
def wdSliceLoopCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))

/-- The two slice stores of one loop iteration. -/
def wdSliceLoopStores : ProgHOL 64 :=
  .seq (.store (.op .add [.var .global (ofString "wd_rlp_slices"),
      .panop .mul [.var .local (ofString "i"), .const (16#64)]])
      (.rfield 0 (.var .local (ofString "e"))))
    (.seq (.store (.op .add [.var .global (ofString "wd_rlp_slices"),
        .panop .mul [.var .local (ofString "i"), .const (16#64)], .const (8#64)])
        (.rfield 1 (.var .local (ofString "e"))))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (1#64)])))

/-- One iteration of the withdrawal loop: encode the record, then store both returned words. -/
def wdSliceLoopBody : ProgHOL 64 :=
  .decCall (ofString "e") (.comb [.one,.one]) (ofString "encode_withdrawal_rlp")
    [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
      .panop .mul [.var .local (ofString "i"), .const (44#64)]]]
    wdSliceLoopStores

/-- The statement-46 withdrawal slice loop. -/
def wdSliceLoop : ProgHOL 64 := .while wdSliceLoopCondition wdSliceLoopBody

theorem source_wd_slice_loop :
    actualPayloadHeaderAt 46 = .seq wdSliceLoop (actualPayloadHeaderAt 47) := by
  rw [source_actual_payload_header_withdrawal_loop]
  rfl

/-- A value whose shape is a two-word combination is exactly a two-word structure. -/
theorem valueWords_of_comb {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one]) = true) :
    ∃ first second : BitVec 64, v = .rStruct [.val (.word first), .val (.word second)] := by
  cases v with
  | val x => simp [shapeOfHOLExact,shapeEqHOL] at h
  | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at h
  | rStruct fields =>
    cases fields with
    | nil => simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    | cons first rest =>
      cases rest with
      | nil => simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
      | cons second rest2 =>
        cases rest2 with
        | cons third rest3 =>
          simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
        | nil =>
          simp only [shapeOfHOLExact,List.map_cons,List.map_nil,shapeEqHOL,
            shapeEqHOL.shapeEqListHOL,Bool.and_eq_true] at h
          obtain ⟨wordFirst, rfl⟩ := shapeWord_of_one h.1
          obtain ⟨wordSecond, rfl⟩ := shapeWord_of_one h.2.1
          exact ⟨wordFirst,wordSecond,rfl⟩

#print axioms source_wd_slice_loop
#print axioms valueWords_of_comb
end InitECandidate.Runtime
