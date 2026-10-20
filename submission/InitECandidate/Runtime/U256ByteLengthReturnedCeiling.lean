import InitECandidate.Runtime.PanReturnedPath
import InitECandidate.Runtime.VmFn_u256_byte_length
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A successful right-shift-by-three return always fits below 2^61. -/
theorem returned_shift_three_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (expression : ExpHOL 64) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.return (.shift .lsr expression (.const (3#64))))=(some (.returned value),post)) :
 ∃word : BitVec 64,value=.val (.word word) ∧word.toNat<2^61 := by
 rw [evaluateHOLFiniteState_return] at run
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
 | none=>simp [evalHOLExact,evaluated] at run
 | some held=>
  cases held with
  | val input=>
   cases input with
   | word input=>
    have output : value=.val (.word (input >>> (3 : Nat))) := by
     simp [evalHOLExact,evaluated,wordShiftHOL] at run
     split at run
     · exact (PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)).symm
     · cases run
    refine ⟨input >>> (3 : Nat),output,?_⟩
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have bound:=input.isLt
    omega
  | rStruct fields=>simp [evalHOLExact,evaluated,wordShiftHOL] at run
  | nStruct name fields=>simp [evalHOLExact,evaluated,wordShiftHOL] at run

/-- The original byte-length routine's actual final shift gives a coarse
 bound without assuming the mathematical value of the 256-bit input. -/
theorem u256_byte_length_returned_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_byte_length)=(some (.returned value),post)) :
 ∃word : BitVec 64,value=.val (.word word) ∧word.toNat<2^61 := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (.decCall (ofString "n") .one (ofString "u256_bit_length")
  [.var .local (ofString "a")] (.return (.shift .lsr (.op .add [.var .local (ofString "n"),.const 7]) (.const (3#64)))))=
  (some (.returned value),post) at run
 obtain ⟨values,body,callee,shape,w,bodyPost,args,lookup,bodyRun,resumed,inner,globals,code,domain,clock,tailRun,rest⟩:=decCall_returned run
 exact returned_shift_three_ceiling resumed inner _ value tailRun
#print axioms returned_shift_three_ceiling
#print axioms u256_byte_length_returned_ceiling
end InitECandidate.Runtime
