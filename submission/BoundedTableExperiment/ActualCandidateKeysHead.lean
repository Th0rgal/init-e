import ActualCandidateProgConversion
namespace BoundedTableExperiment
open InitECandidate.Runtime Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
set_option maxRecDepth 4000

def tAddr (k : Nat) : ExpHOL 64 :=
  .op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 k)]

def strideExpr : ExpHOL 64 :=
  .op .and [.op .add [.var .local (ofString "key_len"), .const (BitVec.ofNat 64 7)],
    .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]]

theorem candidate_htabNewScratch_keysHead :
    ∃ rest, sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch =
      .decCall (ofString "t") .one (ofString "scratch_alloc")
        [.const (BitVec.ofNat 64 120)]
        (.dec (ofString "stride") .one strideExpr
          (.seq (.store (tAddr 0) (.var .local (ofString "key_len")))
            (.seq (.store (tAddr 8) (.var .local (ofString "stride")))
              (.seq (.store (tAddr 16) (.var .local (ofString "cap")))
                (.seq (.store (tAddr 24) (.const (BitVec.ofNat 64 0)))
                  (.decCall (ofString "keys") .one (ofString "scratch_alloc")
                    [.panop .mul [.var .local (ofString "cap"), .var .local (ofString "stride")]]
                    rest)))))) := by
  simp only [sourceFunctionBody, CandidateGuest.guestFn_htab_new_scratch, declToHOL, funDeclToHOL]
  rw [progToHOL_decCall_eq]
  simp only [shapeToHOL, expToHOL, List.map_cons, List.map_nil]
  rw [progToHOL_dec_eq]
  rw [progToHOL_seq_eq, progToHOL_store_eq]
  rw [progToHOL_seq_eq, progToHOL_store_eq]
  rw [progToHOL_seq_eq, progToHOL_store_eq]
  rw [progToHOL_seq_eq, progToHOL_store_eq]
  rw [progToHOL_decCall_eq]
  simp only [shapeToHOL, expToHOL, List.map_cons, List.map_nil]
  exact ⟨_, rfl⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htabNewScratch_keysHead
