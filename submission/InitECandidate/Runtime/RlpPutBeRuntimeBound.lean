import InitECandidate.Runtime.EncFenceBase
import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual reverse byte writer: each successful iteration decreases the unsigned index. -/
def rlpPutBeCondition : ExpHOL 64 := .cmp .lower (.const 0) (.var .local (ofString "i"))
def rlpPutBeDecrement : ProgHOL 64 := .assign .local (ofString "i") (.op .sub [.var .local (ofString "i"),.const 1])
def rlpPutBeStoreShift : ProgHOL 64 := .seq
 (.storeByte (.op .add [.var .local (ofString "dst"),.var .local (ofString "i")]) (.var .local (ofString "v")))
 (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
def rlpPutBeIteration : ProgHOL 64 := .seq rlpPutBeDecrement rlpPutBeStoreShift
def rlpPutBeRank {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
 ∃word : BitVec 64,s.locals.lookup (ofString "i")=some (.val (.word word)) ∧word.toNat=rank

theorem rlp_put_be_ranked {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat)
 (code : s.code=originalRuntimeCode) (valid : rlpPutBeRank s rank) (budget : rank≤s.clock) :
 RankedOutcome s rlpPutBeCondition rank (fun {F} state n=>rlpPutBeRank state n) False
  (evaluateHOLFiniteState s (.while rlpPutBeCondition rlpPutBeIteration)) := by
 have ranked:=rankedWhile_run rlpPutBeCondition rlpPutBeIteration 0
  (fun {F} state n=>rlpPutBeRank state n) False (by
   intro G state ranked word evaluated
   obtain ⟨value,atValue,zero⟩:=ranked
   have eqZero : value=0 := BitVec.eq_of_toNat_eq zero
   subst value
   simp [rlpPutBeCondition,evalHOLFinite,evalHOLExact,atValue,Compiler.Encoders.Asm.wordCmpHOL] at evaluated
   exact evaluated.symm) (by
   intro G state n word installed ranked condition nonzero ticks
   obtain ⟨value,atValue,valueRank⟩:=ranked
   have positive : 0<value.toNat := by
    by_contra bad
    have zero : value=0 := BitVec.eq_of_toNat_eq (by omega)
    subst value
    simp [rlpPutBeCondition,evalHOLFinite,evalHOLExact,atValue,Compiler.Encoders.Asm.wordCmpHOL] at condition
    exact nonzero condition.symm
   let entry:=decClockHOLFinite state
   let decremented:=setVarHOLFinite (ofString "i") (.val (.word (value-1))) entry
   have atEntry : entry.locals.lookup (ofString "i")=some (.val (.word value)) := atValue
   have decrementRun : evaluateHOLFiniteState entry rlpPutBeDecrement=(none,decremented) := by
    simp [rlpPutBeDecrement,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atEntry,wordOpHOL,wordOp,
     valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,decremented]
   have iterationRun : evaluateHOLFiniteState entry rlpPutBeIteration=evaluateHOLFiniteState decremented rlpPutBeStoreShift := by
    rw [rlpPutBeIteration,evaluateHOLFiniteState_seq_line780,decrementRun]
   have bounded:=ProgBounded.straight rlpPutBeIteration rfl entry installed (Nat.zero_le _)
   have noContinue:=evaluate_noTopContinue rlpPutBeIteration rfl entry
   have metadata:=evaluateHOLFiniteState_metadata entry rlpPutBeIteration
   refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
   · intro flowing
     have normal : (evaluateHOLFiniteState entry rlpPutBeIteration).1=none := flowing.resolve_right noContinue
     have frame:=evaluate_avoidsLocal_flowing (ofString "i") rlpPutBeStoreShift rfl decremented
     have nextValue : (evaluateHOLFiniteState entry rlpPutBeIteration).2.locals.lookup (ofString "i")=
       some (.val (.word (value-1))) := by
      rw [iterationRun]
      rw [iterationRun] at normal
      rw [frame (Or.inl normal)]
      simp [decremented,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
     have decreases : (value-1).toNat<value.toNat := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1≤value.toNat;omega))]
      simp;omega
     exact ⟨(value-1).toNat,by omega,⟨value-1,nextValue,rfl⟩,metadata.1⟩
   · intro broken
     exact False.elim (evaluate_noTopBreak rlpPutBeIteration rfl entry broken))
  rank s code valid (by simpa using budget)
 simpa only [Nat.zero_add,Nat.mul_one] using ranked
/-- A deliberately coarse uniform ceiling, valid even for malformed locals.
The source repeatedly shifts right, so successful iterations strictly descend. -/
theorem rlp_put_be_loop_bounded : ProgBounded
 (.while rlpPutBeCondition rlpPutBeIteration) (2^64-1) := by
 intro F state code budget
 cases atValue : state.locals.lookup (ofString "i") with
 | none=>
  simp [evaluateHOLFiniteState_while_total,rlpPutBeCondition,evalHOLExact,atValue]
 | some held=>
  cases held with
  | val value=>
   cases value with
   | word word=>
    have limit : word.toNat≤2^64-1 := by have h:=word.isLt;omega
    have ranked:=rlp_put_be_ranked state word.toNat code ⟨word,atValue,rfl⟩ (limit.trans budget)
    exact ⟨by have spent:=ranked.1;omega,ranked.2.1,ranked.2.2.1⟩
  | rStruct fields=>
   simp [evaluateHOLFiniteState_while_total,rlpPutBeCondition,evalHOLExact,atValue,
    Compiler.Encoders.Asm.wordCmpHOL,valueWord]
  | nStruct size fields=>
   simp [evaluateHOLFiniteState_while_total,rlpPutBeCondition,evalHOLExact,atValue,
    Compiler.Encoders.Asm.wordCmpHOL,valueWord]


/-- Full original byte writer, with arbitrary 64-bit count and failed stores included. -/
theorem rlp_put_be_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_put_be) (2^64-1) := by
 rw [putBeBody_eq]
 change ProgBounded (.dec (ofString "i") .one (.var .local (ofString "n"))
  (.seq (.while rlpPutBeCondition rlpPutBeIteration) (.return (.const 0)))) (2^64-1)
 exact ProgBounded.dec _ _ _ (by
  intro F state code budget
  have composed := ProgBounded.seq rlp_put_be_loop_bounded (ProgBounded.straight (.return (.const 0)) rfl) state code
    (by simpa only [Nat.add_zero] using budget)
  simpa only [Nat.add_zero] using composed)
theorem rlp_put_be_fun_bounded : FunBounded (ofString "rlp_put_be") (2^64-1) :=
 ⟨_,_,_,originalRuntimeCode_rlpPutBe_lookup,rlp_put_be_body_bounded⟩
#print axioms rlp_put_be_body_bounded
#print axioms rlp_put_be_fun_bounded
end InitECandidate.Runtime
