import InitECandidate.Runtime.MemoryCeil32DeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem source_memory_words_of : structuralFunctionBody Guest.guestFn_words_of=
 .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
 (.return (.shift .lsr (.var .local (ofString "c")) (.const 5))) := rfl

/-- Actual words_of returns the shifted real upward-rounded length. -/
theorem memory_words_of_returned_range {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (input : BitVec 64) (value : ValueHOL 64)
 (atInput : s.locals.lookup (ofString "n")=some (.val (.word input)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_words_of)=(some (.returned value),post)) :
 ∃words : BitVec 64,value=.val (.word words) ∧input.toNat/32≤words.toNat ∧words.toNat<2^59 := by
 rw [sourceFunctionBody_eq_structural,source_memory_words_of] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "n")]=some [.val (.word input)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atInput]
 obtain ⟨rounded,bodyPost,output,tailRun,scope,lower,_,_,_,_,_⟩:=memory_ceil32_declaration_returned s post (ofString "c") _ _ input value args code run
 let ready:=setVarHOLFinite (ofString "c") (.val (.word rounded)) {bodyPost with locals:=s.locals}
 change evaluateHOLFiniteState ready (.return (.shift .lsr (.var .local (ofString "c")) (.const 5)))=_ at tailRun
 have evaluated : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.shift .lsr (.var .local (ofString "c")) (.const 5))=some (.val (.word (rounded>>>(5:Nat)))) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,wordShiftHOL]
 have returnRun : evaluateHOLFiniteState ready (.return (.shift .lsr (.var .local (ofString "c")) (.const 5)))=
  (some (.returned (.val (.word (rounded>>>(5:Nat))))),emptyLocalsHOLFinite ready) := by
  rw [evaluateHOLFiniteState_return,evaluated]
  simp [shapeOfHOLExact,sizeOfShapeWithContextHOL]
 have returned:=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (tailRun.symm.trans returnRun)).1)
 refine ⟨_,returned,?_,?_⟩
 all_goals rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 · change input.toNat/32≤rounded.toNat/32;omega
 · have small:=rounded.isLt
   change rounded.toNat/32<2^59
   omega
#print axioms memory_words_of_returned_range
end InitECandidate.Runtime
