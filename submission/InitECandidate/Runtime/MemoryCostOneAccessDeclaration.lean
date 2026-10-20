import InitECandidate.Runtime.MemoryCostOneReturnedAccess
import InitECandidate.Runtime.MemoryCostOneReturnedAligned
import InitECandidate.Runtime.MemoryCostOneBoundedDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem memoryAccessPairFields (a b c d : BitVec 64)
 (same : (.rStruct [.val (.word a),.val (.word b)] : ValueHOL 64)=.rStruct [.val (.word c),.val (.word d)]) : a=c ∧b=d := by
 have fields:=ValueHOL.rStruct.inj same
 exact ⟨HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj fields).1),
  HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj fields).2).1)⟩

/-- Same actual typed cost1 declaration exports span coverage, aligned bounded
expansion, exact lexical continuation and concrete read-only metadata. -/
theorem memory_cost_one_access_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (frame current sa sb sc sd na nb nc nd : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [fundingU256 sa sb sc sd,fundingU256 na nb nc nd])
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (currentAligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one]) (ofString "extend_memory_cost1") arguments tail)=(some (.returned value),post)) :
 ∃fee expansion : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word fee),.val (.word expansion)]) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 current.toNat+expansion.toNat<2^64 ∧expansion.toNat<2^37 ∧expansion.toNat%32=0 ∧
 (fee≠18446744073709551615#64 → evmSatWord na nb nc nd≠0#64 → (evmSatWord sa sb sc sd).toNat+(evmSatWord na nb nc nd).toNat≤current.toNat+expansion.toNat) ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=(HolFiniteMapExact.empty.update (ofString "start",fundingU256 sa sb sc sd)).update (ofString "size",fundingU256 na nb nc nd)
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "extend_memory_cost1") [fundingU256 sa sb sc sd,fundingU256 na nb nc nd]=some (sourceFunctionBody Guest.guestFn_extend_memory_cost1,callee,.comb [.one,.one]) := by
  apply lookupCodeFinite_of_exact
  rw [code]
  simp (config:={decide:=true}) [lookupCodeHOLExact,vmLookup_extend_memory_cost1,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  funext key
  by_cases sizeKey : key=ofString "size"
  · subst key;simp (config:={decide:=true}) [callee,fundingU256,HolFiniteMapExact.lookup_update,FUPDATE]
  · by_cases startKey : key=ofString "start"
    · subst key;simp (config:={decide:=true}) [callee,fundingU256,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp [callee,fundingU256,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,sizeKey,Ne.symm sizeKey,startKey,Ne.symm startKey]
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "extend_memory_cost1") (.comb [.one,.one]) (.comb [.one,.one]) arguments _ _ tail callee value args lookup run
 have atStart : (callEntryStateHOLFinite s callee).locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by
  simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atSize : (callEntryStateHOLFinite s callee).locals.lookup (ofString "size")=some (fundingU256 na nb nc nd) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have smallResult:=memory_cost_one_returned_size_bound (callEntryStateHOLFinite s callee) bodyPost returned code bodyRun
 have alignedResult:=memory_cost_one_returned_aligned (callEntryStateHOLFinite s callee) bodyPost frame current returned atFrame domain currentAt currentAligned code bodyRun
 have accessResult:=memory_cost_one_returned_access (callEntryStateHOLFinite s callee) bodyPost frame current sa sb sc sd na nb nc nd returned atFrame atStart atSize domain currentAt currentAligned code bodyRun
 obtain ⟨fee,expansion,returnedEq,nonwrap⟩:=memory_cost_one_returned_expansion (callEntryStateHOLFinite s callee) bodyPost frame current returned atFrame domain currentAt code bodyRun
 subst returned
 obtain ⟨sizeFee,sizeExpansion,sizeEq,small⟩:=smallResult
 have sizeFields:=memoryAccessPairFields fee expansion sizeFee sizeExpansion sizeEq
 rw [←sizeFields.2] at small
 obtain ⟨alignedFee,alignedExpansion,alignedEq,aligned⟩:=alignedResult
 have alignedFields:=memoryAccessPairFields fee expansion alignedFee alignedExpansion alignedEq
 rw [←alignedFields.2] at aligned
 obtain ⟨accessFee,accessExpansion,accessEq,access⟩:=accessResult
 have accessFields:=memoryAccessPairFields fee expansion accessFee accessExpansion accessEq
 rw [←accessFields.1,←accessFields.2] at access
 have frameKept:=memoryFrame_of_good vmLookup_extend_memory_cost1 (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_extend_memory_cost1)
 rw [bodyRun] at frameKept metadata
 exact ⟨fee,expansion,bodyPost,output,tailRun,postEq,nonwrap,small,aligned,access,frameKept.1,frameKept.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_cost_one_access_declaration_returned
end InitECandidate.Runtime
