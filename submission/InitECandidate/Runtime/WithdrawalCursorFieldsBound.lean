import InitECandidate.Runtime.EncodeHeaderWordAssignmentFrame
import InitECandidate.Runtime.EncodeHeaderBytesAssignmentFrame
import InitECandidate.Runtime.EncodeWithdrawalFinishBound
import InitECandidate.Runtime.EncodeHeaderCursorIncrement
import InitECandidate.Runtime.RlpEncodeBytesFixedCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
inductive WithdrawalFieldWriter where
 | word | address20

def withdrawalFieldCall (writer : WithdrawalFieldWriter) (input : ExpHOL 64) : ProgHOL 64 :=
 match writer with
 | .word=>.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") [.var .local (ofString "p"),input]
 | .address20=>.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") [.var .local (ofString "p"),input,.const 20]
def withdrawalFieldCost : WithdrawalFieldWriter→Nat
 | .word=>rlpWriterSourceCost+1
 | .address20=>rlpEncodeBytesSourceCost 20+1
def withdrawalCursorUpdate : ProgHOL 64 := .assign .local (ofString "p")
 (.op .add [.var .local (ofString "p"),.var .local (ofString "w")])
structure WithdrawalCursorInvariant {F : Type} (s : PanSemStateFiniteExact 64 F) (buffer : BitVec 64) (DF : Nat) : Prop where
 code : s.code=originalRuntimeCode
 fence : Fence s.memaddrs DF
 atBuffer : s.locals.lookup (ofString "buf")=some (.val (.word buffer))
 cursor : ∃pointer : BitVec 64,s.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
  buffer.toNat+9≤pointer.toNat ∧pointer.toNat≤DF+8

theorem withdrawal_field_call_bounded (writer : WithdrawalFieldWriter) (input : ExpHOL 64) :
 ProgBounded (withdrawalFieldCall writer input) (withdrawalFieldCost writer) := by
 cases writer with
 | word=>intro F state code budget;exact ProgBounded.call rlp_encode_word_fun_bounded _ _ state code budget
 | address20=>intro F state code budget;exact ProgBounded.rlpEncodeBytesFixedCall _ _ _ 20 (by decide) state code budget

/-- A successful actual field writer supplies its returned word; the actual
 p update then preserves the buffer and advances without word wrap. -/
theorem withdrawal_field_normal_advance {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (writer : WithdrawalFieldWriter) (input : ExpHOL 64) (buffer : BitVec 64) (DF : Nat)
 (valid : WithdrawalCursorInvariant s buffer DF) (cap : DF+8≤2^62)
 (run : evaluateHOLFiniteState s (withdrawalFieldCall writer input)=(none,post)) :
 ∃next,evaluateHOLFiniteState post withdrawalCursorUpdate=(none,next) ∧WithdrawalCursorInvariant next buffer DF := by
 obtain ⟨pointer,atP,low,high⟩:=valid.cursor
 have framed : ∃written : BitVec 64,pointer.toNat+written.toNat≤DF+8 ∧
  post.locals=s.locals.update (ofString "w",.val (.word written)) := by
  cases writer with
  | word=>
   obtain ⟨written,fits,locals,_,_⟩:=encode_header_word_assignment_frame s post input pointer 8 0 DF
    valid.code valid.fence (by omega) (by decide) (by decide) (by change 8≤pointer.toNat;omega) high atP run
   exact ⟨written,fits,locals⟩
  | address20=>
   obtain ⟨written,fits,locals,_,_⟩:=encode_header_bytes_assignment_frame s post input pointer 20 8 0 DF
    valid.code valid.fence (by omega) (by decide) (by decide) (by change 8≤pointer.toNat;omega) high atP run
   exact ⟨written,fits,locals⟩
 obtain ⟨written,fits,locals⟩:=framed
 have keptP : post.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
  rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atP
 have atW : post.locals.lookup (ofString "w")=some (.val (.word written)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have increment:=encode_header_cursor_increment post pointer written DF (by omega) keptP atW fits
 have metadata:=evaluateHOLFiniteState_metadata s (withdrawalFieldCall writer input)
 rw [run] at metadata
 refine ⟨setVarHOLFinite (ofString "p") (.val (.word (pointer+written))) post,increment.1,?_,?_,?_,?_⟩
 · exact metadata.1.trans valid.code
 · change Fence post.memaddrs DF;rw [metadata.2.1];exact valid.fence
 · change (post.locals.update (ofString "p",.val (.word (pointer+written)))).lookup (ofString "buf")=_
   rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using valid.atBuffer
 · refine ⟨pointer+written,?_,?_,?_⟩
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · rw [increment.2];omega
   · rw [increment.2];exact fits

def withdrawalFieldsProgram : List (WithdrawalFieldWriter×ExpHOL 64)→ProgHOL 64
 | []=>encodeWithdrawalAt 10
 | (writer,input)::rest=>.seq (withdrawalFieldCall writer input) (.seq withdrawalCursorUpdate (withdrawalFieldsProgram rest))
def withdrawalFieldsCost (DF : Nat) : List (WithdrawalFieldWriter×ExpHOL 64)→Nat
 | []=>encodeWithdrawalFinishCost (DF+8)
 | (writer,_)::rest=>withdrawalFieldCost writer+withdrawalFieldsCost DF rest

/-- Every writer in this concrete sequence is discharged by its actual runtime
 and normal-return cursor theorem; the list finisher gets its size from them. -/
theorem withdrawal_fields_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (fields : List (WithdrawalFieldWriter×ExpHOL 64)) (buffer : BitVec 64) (DF : Nat)
 (valid : WithdrawalCursorInvariant s buffer DF) (cap : DF+8≤2^62)
 (budget : withdrawalFieldsCost DF fields≤s.clock) :
 RunBounded s (withdrawalFieldsProgram fields) (withdrawalFieldsCost DF fields) := by
 induction fields generalizing s with
 | nil=>
  obtain ⟨pointer,atP,low,high⟩:=valid.cursor
  exact encode_withdrawal_finish_bounded s buffer pointer (DF+8) valid.atBuffer atP valid.code cap low high budget
 | cons field rest ih=>
  obtain ⟨writer,input⟩:=field
  change RunBounded s (.seq (withdrawalFieldCall writer input) (.seq withdrawalCursorUpdate (withdrawalFieldsProgram rest))) _
  apply RunBounded.seq (withdrawal_field_call_bounded writer input s valid.code (by change withdrawalFieldCost writer+withdrawalFieldsCost DF rest≤s.clock at budget;omega)) budget
  intro post normal _ remaining
  obtain ⟨next,increment,nextValid⟩:=withdrawal_field_normal_advance s post writer input buffer DF valid cap normal
  have first : RunBounded post withdrawalCursorUpdate 0 := by
   have straight : ProgBounded withdrawalCursorUpdate 0 := ProgBounded.straight _ rfl
   have metadata:=evaluateHOLFiniteState_metadata s (withdrawalFieldCall writer input)
   rw [normal] at metadata
   exact straight post (metadata.1.trans valid.code) (Nat.zero_le _)
  have paired : RunBounded post (.seq withdrawalCursorUpdate (withdrawalFieldsProgram rest)) (0+withdrawalFieldsCost DF rest) := by
   apply RunBounded.seq first (by simpa only [Nat.zero_add] using remaining)
   intro actual actualRun _ ticks
   rw [increment] at actualRun
   have equal := (Prod.mk.inj actualRun).2
   subst equal
   exact ih next nextValid ticks
  simpa only [Nat.zero_add] using paired
def withdrawalActualFieldInput (index : Nat) : ExpHOL 64 :=
 match encodeWithdrawalAt index with
 | .seq (.call _ _ (_::input::_)) _=>input
 | _=>.const 0
def withdrawalActualAssignedFields : List (WithdrawalFieldWriter×ExpHOL 64) :=
 [(.word,withdrawalActualFieldInput 4),(.address20,withdrawalActualFieldInput 6),(.word,withdrawalActualFieldInput 8)]
theorem source_withdrawal_assigned_fields : encodeWithdrawalAt 4=withdrawalFieldsProgram withdrawalActualAssignedFields := rfl

/-- The three actual assigned writers and following list finisher, including
 the original SSZ little-endian expressions, have no unproved callee premise. -/
theorem encode_withdrawal_assigned_fields_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (buffer : BitVec 64) (DF : Nat) (valid : WithdrawalCursorInvariant s buffer DF) (cap : DF+8≤2^62)
 (budget : withdrawalFieldsCost DF withdrawalActualAssignedFields≤s.clock) :
 RunBounded s (encodeWithdrawalAt 4) (withdrawalFieldsCost DF withdrawalActualAssignedFields) := by
 rw [source_withdrawal_assigned_fields]
 exact withdrawal_fields_bounded s withdrawalActualAssignedFields buffer DF valid cap budget
#print axioms encode_withdrawal_assigned_fields_bounded
#print axioms withdrawal_field_normal_advance
#print axioms withdrawal_fields_bounded
end InitECandidate.Runtime
