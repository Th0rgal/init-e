import InitECandidate.Runtime.MemoryCostOneEndpointCovers
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def MemoryExpansionAccess (current start size : BitVec 64) (value : ValueHOL 64) : Prop :=
 ∃fee expansion : BitVec 64,value=.rStruct [.val (.word fee),.val (.word expansion)] ∧
  (fee≠18446744073709551615#64 → size≠0#64 → start.toNat+size.toNat≤current.toNat+expansion.toNat)

/-- Actual saturation of both U256 arguments, actual checked add_sat endpoint,
rounding and fee guards yield natural access-span coverage. -/
theorem memory_cost_one_preparation_span {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current sa sb sc sd na nb nc nd : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atStart : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (atSize : s.locals.lookup (ofString "size")=some (fundingU256 na nb nc nd))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 2)=(some (.returned value),post)) :
 MemoryExpansionSpan current (evmSatWord sa sb sc sd) (evmSatWord na nb nc nd) value := by
 rw [source_memory_cost_one_2] at run
 have argsStart : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "start")]=some [fundingU256 sa sb sc sd] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atStart]
 obtain ⟨firstPost,firstOutput,firstRun,firstScope,firstMemory,firstGlobals,firstCode,firstDomain,_⟩:=funding_sat_word_declaration_geometry s post (ofString "s") _ (memoryCostOneAt 3) sa sb sc sd value argsStart code run
 let first:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord sa sb sc sd))) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 3)=_ at firstRun
 have sizeAt : first.locals.lookup (ofString "size")=some (fundingU256 na nb nc nd) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSize
 have argsSize : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.var .local (ofString "size")]=some [fundingU256 na nb nc nd] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,sizeAt]
 rw [source_memory_cost_one_3] at firstRun
 obtain ⟨secondPost,secondOutput,secondRun,secondScope,secondMemory,secondGlobals,secondCode,secondDomain,_⟩:=funding_sat_word_declaration_geometry first firstOutput (ofString "n") _ (memoryCostOneAt 4) na nb nc nd value argsSize (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "n") (.val (.word (evmSatWord na nb nc nd))) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 4)=_ at secondRun
 have startAt : second.locals.lookup (ofString "s")=some (.val (.word (evmSatWord sa sb sc sd))) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have sizeAt : second.locals.lookup (ofString "n")=some (.val (.word (evmSatWord na nb nc nd))) := by
  simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have sameMemory : second.memory=s.memory:=secondMemory.trans firstMemory
 have sameGlobals : second.globals=s.globals:=secondGlobals.trans firstGlobals
 have sameDomain : second.memaddrs=s.memaddrs:=secondDomain.trans firstDomain
 apply memory_cost_one_added_span second secondOutput frame current (evmSatWord sa sb sc sd) (evmSatWord na nb nc nd) value _ startAt sizeAt _ _ aligned (secondCode.trans (firstCode.trans code)) secondRun
 · rw [sameGlobals];exact atFrame
 · rw [sameDomain];exact domain
 · rw [sameMemory];exact currentAt

/-- Whole original cost1 access contract on real word-valued U256 arguments.
A nonMAX actual fee covers every nonempty actual saturated access; the original
zero-size early return remains vacuous only for an actual empty access. -/
theorem memory_cost_one_returned_access {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current sa sb sc sd na nb nc nd : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atStart : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (atSize : s.locals.lookup (ofString "size")=some (fundingU256 na nb nc nd))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_extend_memory_cost1)=(some (.returned value),post)) :
 MemoryExpansionAccess current (evmSatWord sa sb sc sd) (evmSatWord na nb nc nd) value := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCostOneAt 0)=_ at run
 rw [source_memory_cost_one_0] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "size")]=some [fundingU256 na nb nc nd] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atSize]
 obtain ⟨firstPost,firstOutput,firstRun,firstScope,memory,globals,firstCode,mapped,_⟩:=funding_u256_zero_declaration_geometry s post (ofString "z") _ (memoryCostOneAt 1) na nb nc nd value args code run
 let first:=setVarHOLFinite (ofString "z") (.val (.word (fundingU256ZeroFlag na nb nc nd))) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 1)=_ at firstRun
 have z : first.locals.lookup (ofString "z")=some (.val (.word (fundingU256ZeroFlag na nb nc nd))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have condition : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.cmp .notEqual (.var .local (ofString "z")) (.const 0))=some (.val (.word (if fundingU256ZeroFlag na nb nc nd=0#64 then 0 else 1))) := by
  simp [evalHOLExact,z,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_one_1] at firstRun
 rcases memory_cost_guard_returned_choice first firstOutput _ _ 0 (memoryCostOneAt 2) value condition firstRun with ⟨nonzero,returned⟩|⟨_,tailRun⟩
 · have sizeZero : evmSatWord na nb nc nd=0#64 := by
    by_cases zero : na|||nb|||nc|||nd=0#64
    · simp only [BitVec.or_eq_zero_iff,and_assoc] at zero
      rcases zero with ⟨rfl,rfl,rfl,rfl⟩
      simp [evmSatWord]
    · simp [fundingU256ZeroFlag,zero] at nonzero
   rw [returned]
   exact ⟨0,0,rfl,fun _ nonempty=>False.elim (nonempty sizeZero)⟩
 · have startAt : first.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by
    simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atStart
   have sizeAt : first.locals.lookup (ofString "size")=some (fundingU256 na nb nc nd) := by
    simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSize
   obtain ⟨fee,expansion,returned,span⟩:=memory_cost_one_preparation_span first firstOutput frame current sa sb sc sd na nb nc nd value
    (by change firstPost.globals.lookup _=_;rw [globals];exact atFrame) startAt sizeAt
    (by change firstPost.memaddrs _;rw [mapped];exact domain)
    (by change firstPost.memory _=_;rw [memory];exact currentAt) aligned (firstCode.trans code) tailRun
   exact ⟨fee,expansion,returned,fun notMaximum _=>span notMaximum⟩
#print axioms memory_cost_one_preparation_span
#print axioms memory_cost_one_returned_access
end InitECandidate.Runtime
