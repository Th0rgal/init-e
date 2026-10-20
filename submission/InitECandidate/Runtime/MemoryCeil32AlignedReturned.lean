import InitECandidate.Runtime.FundingAllocationReturnedContext
import InitECandidate.Runtime.FrameNewSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def memoryCeil32At (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_ceil32)

theorem source_memory_ceil32_0 : memoryCeil32At 0=.dec (ofString "r") .one
 (.op .and [.var .local (ofString "v"),.const 31]) (memoryCeil32At 1):=rfl
theorem source_memory_ceil32_1 : memoryCeil32At 1=.seq
 (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0)) (.return (.var .local (ofString "v"))) .skip)
 (memoryCeil32At 2):=rfl

/-- The actual ceil32 helper returns an already 32-byte-aligned size unchanged,
before its add_sat call; there is no callee/code/fuel premise. -/
theorem memory_ceil32_aligned_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (input : BitVec 64) (value : ValueHOL 64)
 (atInput : s.locals.lookup (ofString "v")=some (.val (.word input)))
 (aligned : input.toNat%32=0)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_ceil32)=(some (.returned value),post)) :
 value=.val (.word input) := by
 have bits : input&&&31#64=0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change input.toNat&&&(2^5-1)=0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact aligned
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCeil32At 0)=_ at run
 rw [source_memory_ceil32_0] at run
 obtain ⟨r,output,evalR,nextRun,scope⟩:=funding_declaration_returned_context run
 have andDef (x y : BitVec 64) : AndOp.and x y=x&&&y := rfl
 have rEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .and [.var .local (ofString "v"),.const 31])=some (.val (.word 0)) := by
  simp [evalHOLExact,evalListHOLExact,atInput,wordOpHOL,wordOp,valueIsWord,valueWord,andDef,bits]
 have equal : r=.val (.word 0):=Option.some.inj (evalR.symm.trans rEval)
 subst r
 let first:=setVarHOLFinite (ofString "r") (.val (.word 0)) s
 change evaluateHOLFiniteState first (memoryCeil32At 1)=_ at nextRun
 have atInputFirst : first.locals.lookup (ofString "v")=some (.val (.word input)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atInput
 have atR : first.locals.lookup (ofString "r")=some (.val (.word 0)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have cmp : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.cmp .equal (.var .local (ofString "r")) (.const 0))=some (.val (.word 1)) := by
  simp [evalHOLExact,atR,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_ceil32_1,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,cmp] at nextRun
 simp [evaluateHOLFiniteState_return,evalHOLExact,atInputFirst,shapeOfHOLExact] at nextRun
 exact PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj nextRun).1).symm
#print axioms memory_ceil32_aligned_returned
end InitECandidate.Runtime
