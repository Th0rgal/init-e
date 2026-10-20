import InitECandidate.Runtime.MemoryCostTwoTemporarySize
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Whole original two-region memory cost helper. Its actual first expansion
is stored only temporarily, the real second cost1 call bounds the combined
expansion, and the original length is restored before every final return. -/
theorem memory_cost_two_returned_size_bound {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_extend_memory_cost2)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^38) value := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCostTwoAt 0)=_ at run
 rw [source_memory_cost_two_0] at run
 obtain ⟨fee,expansion,bodyPost,output,tailRun,postEq,bounded,sizeBound,memory,globals,installed,mapped,_⟩:=
  memory_cost_one_bounded_declaration_returned s post (ofString "a") _ (memoryCostTwoAt 1) frame current value atFrame domain currentAt code run
 let ready:=setVarHOLFinite (ofString "a") (.rStruct [.val (.word fee),.val (.word expansion)]) {bodyPost with locals:=s.locals}
 change evaluateHOLFiniteState ready (memoryCostTwoAt 1)=_ at tailRun
 have pair : ready.locals.lookup (ofString "a")=some (.rStruct [.val (.word fee),.val (.word expansion)]) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have cmp : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615))=
  some (.val (.word (if fee=18446744073709551615#64 then 1 else 0))) := by
  simp [evalHOLExact,pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_two_1] at tailRun
 rcases memory_cost_pair_guard_memory_returned ready output _ _ fee expansion (ofString "a") (memoryCostTwoAt 2) value pair cmp tailRun with ⟨returned,memoryKept,globalsKept⟩|⟨_,nextRun⟩
 · exact ⟨fee,expansion,returned,by omega⟩
 · have result:=memory_cost_two_temporary_size ready output frame current fee expansion value
    (by change bodyPost.globals.lookup _=_;rw [globals];exact atFrame)
    (by change bodyPost.memaddrs _;rw [mapped];exact domain)
    (by change bodyPost.memory _=_;rw [memory];exact currentAt) pair bounded sizeBound (installed.trans code) nextRun
   exact result
#print axioms memory_cost_two_returned_size_bound
end InitECandidate.Runtime
