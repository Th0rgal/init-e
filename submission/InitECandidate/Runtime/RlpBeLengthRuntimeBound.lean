import InitECandidate.Runtime.EncFenceBase
import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.StraightLocalOutcomes
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual byte-length loop, separated only at its structural source spine. -/
def rlpBeLengthCondition : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "v")) (.const 0)
def rlpBeLengthShift : ProgHOL 64 := .assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))
def rlpBeLengthIncrement : ProgHOL 64 := .assign .local (ofString "n") (.op .add [.var .local (ofString "n"),.const 1])
def rlpBeLengthIteration : ProgHOL 64 := .seq rlpBeLengthShift rlpBeLengthIncrement
def rlpBeLengthRank {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
 ∃word : BitVec 64,s.locals.lookup (ofString "v")=some (.val (.word word)) ∧word.toNat=rank

theorem rlp_be_length_ranked {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat)
 (code : s.code=originalRuntimeCode) (valid : rlpBeLengthRank s rank) (budget : rank≤s.clock) :
 RankedOutcome s rlpBeLengthCondition rank (fun {F} state n=>rlpBeLengthRank state n) False
  (evaluateHOLFiniteState s (.while rlpBeLengthCondition rlpBeLengthIteration)) := by
 have ranked:=rankedWhile_run rlpBeLengthCondition rlpBeLengthIteration 0
  (fun {F} state n=>rlpBeLengthRank state n) False (by
   intro G state ranked word evaluated
   obtain ⟨value,atValue,zero⟩:=ranked
   have eqZero : value=0 := BitVec.eq_of_toNat_eq zero
   subst value
   simp [rlpBeLengthCondition,evalHOLFinite,evalHOLExact,atValue,Compiler.Encoders.Asm.wordCmpHOL] at evaluated
   exact evaluated.symm) (by
   intro G state n word installed ranked condition nonzero ticks
   obtain ⟨value,atValue,valueRank⟩:=ranked
   let entry:=decClockHOLFinite state
   let shifted:=setVarHOLFinite (ofString "v") (.val (.word (value >>> (8 : Nat)))) entry
   have atEntry : entry.locals.lookup (ofString "v")=some (.val (.word value)) := atValue
   have shiftedRun : evaluateHOLFiniteState entry rlpBeLengthShift=(none,shifted) := by
    simp [rlpBeLengthShift,evaluateHOLFiniteState_assign,evalHOLExact,atEntry,wordShiftHOL,lookupKvarHOLExact,
     isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,shifted]
   have iterationRun : evaluateHOLFiniteState entry rlpBeLengthIteration=evaluateHOLFiniteState shifted rlpBeLengthIncrement := by
    rw [rlpBeLengthIteration,evaluateHOLFiniteState_seq_line780,shiftedRun]
   have bounded:=ProgBounded.straight rlpBeLengthIteration rfl entry installed (Nat.zero_le _)
   have outcomes:=evaluate_straightLocal_outcomes rlpBeLengthIteration rfl entry
   have metadata:=evaluateHOLFiniteState_metadata entry rlpBeLengthIteration
   refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
   · intro flowing
     have normal : (evaluateHOLFiniteState entry rlpBeLengthIteration).1=none := by
      rcases flowing with normal|continued
      · exact normal
      · rcases outcomes with normal|error
        · rw [normal] at continued;cases continued
        · rw [error] at continued;cases continued
     have frame:=evaluate_avoidsLocal_flowing (ofString "v") rlpBeLengthIncrement (by rfl) shifted
     have nextValue : (evaluateHOLFiniteState entry rlpBeLengthIteration).2.locals.lookup (ofString "v")=
       some (.val (.word (value >>> (8 : Nat)))) := by
      rw [iterationRun]
      rw [iterationRun] at normal
      rw [frame (Or.inl normal)]
      simp [shifted,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
     have decreases : (value >>> (8 : Nat)).toNat<value.toNat := by
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_self (by omega) (by decide)
     exact ⟨(value >>> (8 : Nat)).toNat,by omega,⟨value >>> (8 : Nat),nextValue,rfl⟩,metadata.1⟩
   · intro broken
     rcases outcomes with normal|error
     · rw [normal] at broken;cases broken
     · rw [error] at broken;cases broken)
  rank s code valid (by simpa using budget)
 simpa only [Nat.zero_add,Nat.mul_one] using ranked
/-- A deliberately coarse uniform ceiling, valid even for malformed locals.
The source repeatedly shifts right, so successful iterations strictly descend. -/
theorem rlp_be_length_loop_bounded : ProgBounded
 (.while rlpBeLengthCondition rlpBeLengthIteration) (2^64-1) := by
 intro F state code budget
 cases atValue : state.locals.lookup (ofString "v") with
 | none=>
  simp [evaluateHOLFiniteState_while_total,rlpBeLengthCondition,evalHOLExact,atValue]
 | some held=>
  cases held with
  | val value=>
   cases value with
   | word word=>
    have limit : word.toNat≤2^64-1 := by have h:=word.isLt;omega
    have ranked:=rlp_be_length_ranked state word.toNat code ⟨word,atValue,rfl⟩ (limit.trans budget)
    exact ⟨by have spent:=ranked.1;omega,ranked.2.1,ranked.2.2.1⟩
  | rStruct fields=>
   simp [evaluateHOLFiniteState_while_total,rlpBeLengthCondition,evalHOLExact,atValue,
    Compiler.Encoders.Asm.wordCmpHOL,valueWord]
  | nStruct size fields=>
   simp [evaluateHOLFiniteState_while_total,rlpBeLengthCondition,evalHOLExact,atValue,
    Compiler.Encoders.Asm.wordCmpHOL,valueWord]

/-- The complete original byte-length helper, including declaration and return,
has a finite source-step ceiling with no input or memory precondition. -/
theorem rlp_be_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_be_len) (2^64-1) := by
 intro F state code budget
 rw [beLenBody_eq]
 change state.clock≤(evaluateHOLFiniteState state (.dec (ofString "n") .one (.const 0)
  (.seq (.while rlpBeLengthCondition rlpBeLengthIteration) (.return (.var .local (ofString "n")))))).2.clock+(2^64-1) ∧
  (evaluateHOLFiniteState state (.dec (ofString "n") .one (.const 0)
  (.seq (.while rlpBeLengthCondition rlpBeLengthIteration) (.return (.var .local (ofString "n")))))).2.clock≤state.clock ∧
  (evaluateHOLFiniteState state (.dec (ofString "n") .one (.const 0)
  (.seq (.while rlpBeLengthCondition rlpBeLengthIteration) (.return (.var .local (ofString "n")))))).1≠some .timeOut
 rw [evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 have sequence : ProgBounded (.seq (.while rlpBeLengthCondition rlpBeLengthIteration)
   (.return (.var .local (ofString "n")))) ((2^64-1)+0) :=
  ProgBounded.seq rlp_be_length_loop_bounded (ProgBounded.straight (.return (.var .local (ofString "n"))) rfl)
 have checked:=sequence (setVarHOLFinite (ofString "n") (.val (.word (0#64))) state) code
  (by simpa [setVarHOLFinite] using budget)
 simpa [setVarHOLFinite] using checked

theorem rlp_be_length_fun_bounded : FunBounded (ofString "rlp_be_len") (2^64-1) :=
 ⟨_,_,_,originalRuntimeCode_rlpBeLen_lookup,rlp_be_length_body_bounded⟩
#print axioms rlp_be_length_ranked
#print axioms rlp_be_length_loop_bounded
#print axioms rlp_be_length_body_bounded
#print axioms rlp_be_length_fun_bounded
end InitECandidate.Runtime
