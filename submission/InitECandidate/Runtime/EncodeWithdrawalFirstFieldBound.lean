import InitECandidate.Runtime.WithdrawalCursorFieldsBound
import InitECandidate.Runtime.RlpWordAssignmentCursor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def withdrawalFirstInput : ExpHOL 64 := match encodeWithdrawalAt 2 with
 | .decCall _ _ _ (_::input::_) _=>input
 | _=>.const 0
def withdrawalFirstFieldsCost (DF : Nat) := rlpWriterSourceCost+1+withdrawalFieldsCost DF withdrawalActualAssignedFields

theorem source_withdrawal_first_field : encodeWithdrawalAt 2=
 .decCall (ofString "w") .one (ofString "rlp_encode_word") [.var .local (ofString "p"),withdrawalFirstInput]
  (.seq withdrawalCursorUpdate (encodeWithdrawalAt 4)) := rfl

/-- The first real declared word writer and all remaining original withdrawal
 fields. Its returned cursor is obtained from the callee execution itself. -/
theorem encode_withdrawal_first_field_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (buffer : BitVec 64) (DF : Nat) (valid : WithdrawalCursorInvariant s buffer DF) (cap : DF+8≤2^62)
 (budget : withdrawalFirstFieldsCost DF≤s.clock) :
 RunBounded s (encodeWithdrawalAt 2) (withdrawalFirstFieldsCost DF) := by
 rw [source_withdrawal_first_field]
 obtain ⟨pointer,atP,low,high⟩:=valid.cursor
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) withdrawalFirstInput with
 | none=>
  have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "p"),withdrawalFirstInput]=none := by
   simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated]
  unfold RunBounded
  rw [evaluateHOLFiniteState_decCall_args_none s _ _ _ _ _ args]
  simp
 | some input=>
  have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "p"),withdrawalFirstInput]=
   some [.val (.word pointer),input] := by
   simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated]
  apply RunBounded.decCall args budget
  intro body callee shape lookup
  have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_word") _ _ body _ shape _ callee
   (by rw [valid.code];exact originalRuntimeCode_rlpEncodeWord_lookup) lookup
  subst same
  have bound:=ProgBounded.bodies_of_fun rlp_encode_word_fun_bounded s valid.code (by unfold withdrawalFirstFieldsCost at budget;omega)
   _ _ _ _ lookup
  refine ⟨bound,?_⟩
  intro returned post bodyRun remaining
  have originalLookup:=lookup
  rw [valid.code] at originalLookup
  have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeWord_lookup originalLookup
  simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at shapes
  obtain ⟨inputWord,rfl⟩:=word_of_shape_one ((shapeEqHOL_eq_true _ _).mp shapes.2).symm
  have bindings:=callee_eq originalRuntimeCode_rlpEncodeWord_lookup originalLookup
  let entry:=callEntryStateHOLFinite s callee
  have framed:=encode_header_word_body_returned_frame entry post pointer inputWord 8 0 DF returned
   valid.code valid.fence (by omega) (by decide) (by decide) (by change 8≤pointer.toNat;omega) high
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
  obtain ⟨written,rfl,fits⟩:=framed.1
  let resumed:=setVarHOLFinite (ofString "w") (.val (.word written)) {post with locals:=s.locals}
  have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_encode_word)
  rw [bodyRun] at metadata
  have resumeCode : resumed.code=originalRuntimeCode := metadata.1.trans valid.code
  have resumeFence : Fence resumed.memaddrs DF := by change Fence post.memaddrs DF;rw [metadata.2.1];exact valid.fence
  have resumeP : resumed.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
   simpa (config:={decide:=true}) [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atP
  have resumeW : resumed.locals.lookup (ofString "w")=some (.val (.word written)) := by
   simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have increment:=encode_header_cursor_increment resumed pointer written DF (by omega) resumeP resumeW fits
  have first : RunBounded resumed withdrawalCursorUpdate 0 := by
   exact ProgBounded.straight _ rfl resumed resumeCode (Nat.zero_le _)
  have result : RunBounded resumed (.seq withdrawalCursorUpdate (encodeWithdrawalAt 4))
   (0+withdrawalFieldsCost DF withdrawalActualAssignedFields) := by
   apply RunBounded.seq first (by simpa only [Nat.zero_add,resumed,setVarHOLFinite] using remaining)
   intro actual actualRun _ ticks
   rw [withdrawalCursorUpdate,increment.1] at actualRun
   have equal:=(Prod.mk.inj actualRun).2
   subst equal
   apply encode_withdrawal_assigned_fields_bounded _ buffer DF ?_ cap ticks
   refine ⟨resumeCode,resumeFence,?_,pointer+written,?_,?_,?_⟩
   · simpa (config:={decide:=true}) [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using valid.atBuffer
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · rw [increment.2];omega
   · rw [increment.2];exact fits
  simpa only [Nat.zero_add] using result
#print axioms encode_withdrawal_first_field_bounded
end InitECandidate.Runtime
