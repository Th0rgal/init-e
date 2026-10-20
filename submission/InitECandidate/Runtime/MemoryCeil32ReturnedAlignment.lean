import InitECandidate.Runtime.MemoryCeil32ReturnedLower
import InitECandidate.Runtime.MemoryCeil32AlignedReturned
import InitECandidate.Runtime.AddSat
import InitECandidate.Runtime.VmFn_add_sat
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual ceil32 return is saturated MAX or aligned to32. Normal finite
charged memory growth will exclude the MAX branch using its real fee guard. -/
theorem memory_ceil32_returned_alignment {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (input : BitVec 64) (value : ValueHOL 64)
 (atInput : s.locals.lookup (ofString "v")=some (.val (.word input)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_ceil32)=(some (.returned value),post)) :
 ∃rounded : BitVec 64,value=.val (.word rounded) ∧(rounded=18446744073709551615#64 ∨rounded.toNat%32=0) := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCeil32At 0)=_ at run
 rw [source_memory_ceil32_0] at run
 obtain ⟨r,output,evalR,nextRun,scope⟩:=funding_declaration_returned_context run
 have andDef (x y : BitVec 64) : AndOp.and x y=x&&&y := rfl
 have rEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .and [.var .local (ofString "v"),.const 31])=some (.val (.word (input&&&31#64))) := by
  simp [evalHOLExact,evalListHOLExact,atInput,wordOpHOL,wordOp,valueIsWord,valueWord,andDef]
 have equal : r=.val (.word (input&&&31#64)):=Option.some.inj (evalR.symm.trans rEval)
 subst r
 let first:=setVarHOLFinite (ofString "r") (.val (.word (input&&&31#64))) s
 change evaluateHOLFiniteState first (memoryCeil32At 1)=_ at nextRun
 have v : first.locals.lookup (ofString "v")=some (.val (.word input)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atInput
 have rr : first.locals.lookup (ofString "r")=some (.val (.word (input&&&31#64))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 by_cases zero : input&&&31#64=0#64
 · have cmp : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
    (.cmp .equal (.var .local (ofString "r")) (.const 0))=some (.val (.word 1)) := by
    simp [evalHOLExact,rr,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
   rw [source_memory_ceil32_1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp] at nextRun
   have returned : value=.val (.word input) := by
    simpa [evaluateHOLFiniteState_return,evalHOLExact,v,shapeOfHOLExact] using (Prod.mk.inj nextRun).1.symm
   refine ⟨input,returned,Or.inr ?_⟩
   have natural:=congrArg BitVec.toNat zero
   rw [BitVec.toNat_and] at natural
   change input.toNat&&&(2^5-1)=0 at natural
   rw [Nat.and_two_pow_sub_one_eq_mod] at natural
   exact natural
 · have cmp : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
    (.cmp .equal (.var .local (ofString "r")) (.const 0))=some (.val (.word 0)) := by
    simp [evalHOLExact,rr,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
   rw [source_memory_ceil32_1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp] at nextRun
   simp only [if_pos rfl,evaluateHOLFiniteState_skip] at nextRun
   change evaluateHOLFiniteState first (memoryCeil32At 2)=_ at nextRun
   rw [source_memory_ceil32_2] at nextRun
   have args : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a))
    [.var .local (ofString "v"),.op .sub [.const 32,.var .local (ofString "r")]]=
    some [.val (.word input),.val (.word (32#64-(input&&&31#64)))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,v,rr,wordOpHOL,wordOp,valueIsWord,valueWord]
   have installed : first.code.lookup (ofString "add_sat")=some addSatCodeEntry := by
    change s.code.lookup _=_;rw [code];exact vmLookup_add_sat
   have ticks : first.clock≠0 := by
    intro noClock
    rw [evaluateHOLFiniteState_decCall_total,args] at nextRun
    dsimp only at nextRun
    rw [lookup_source_addSat first.code.lookup input (32#64-(input&&&31#64)) installed] at nextRun
    simp [noClock] at nextRun
   rw [evaluate_addSat_decCall first (ofString "s") _ _ input (32#64-(input&&&31#64)) installed args ticks] at nextRun
   have returned : value=.val (.word (wordAddSat input (32#64-(input&&&31#64)))) := by
    simpa [evaluateHOLFiniteState_return,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact] using (Prod.mk.inj nextRun).1.symm
   let padding:=32#64-(input&&&31#64)
   let rounded:=wordAddSat input padding
   refine ⟨rounded,returned,?_⟩
   by_cases saturated : rounded=18446744073709551615#64
   · exact Or.inl saturated
   · right
     have remainder : (input&&&31#64).toNat=input.toNat%32 := by
      rw [BitVec.toNat_and]
      change input.toNat&&&(2^5-1)=input.toNat%32
      exact Nat.and_two_pow_sub_one_eq_mod input.toNat 5
     have remBound : (input&&&31#64).toNat<32 := by rw [remainder];omega
     have padNat : padding.toNat=32-input.toNat%32 := by
      change (32#64-(input&&&31#64)).toNat=_
      rw [BitVec.toNat_sub_of_le (by change (input&&&31#64).toNat≤32;omega)]
      change 32-(input&&&31#64).toNat=_
      rw [remainder]
     have belowMax : rounded.toNat<18446744073709551615 := by
      have bounded:=rounded.isLt
      have different : rounded.toNat≠18446744073709551615 := by
       intro same
       apply saturated
       apply BitVec.eq_of_toNat_eq
       exact same
      omega
     have sum : rounded.toNat=input.toNat+padding.toNat := by
      have value:=wordAddSat_toNat input padding
      change rounded.toNat=min (input.toNat+padding.toNat) (2^64-1) at value
      omega
     rw [sum,padNat]
     have positive : input.toNat%32≠0 := by
      intro aligned
      apply zero
      apply BitVec.eq_of_toNat_eq
      rw [remainder]
      exact aligned
     omega

#print axioms memory_ceil32_returned_alignment
end InitECandidate.Runtime
