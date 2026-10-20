import InitECandidate.Runtime.MemoryCostTwoSource
import InitECandidate.Runtime.MemoryCostPairGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Original two-region final guard and returned tuple. The second expansion
was checked against the actually increased temporary current length. -/
theorem memory_cost_two_tail_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current firstFee firstExpansion secondFee secondExpansion : BitVec 64) (value : ValueHOL 64)
 (atA : s.locals.lookup (ofString "a")=some (.rStruct [.val (.word firstFee),.val (.word firstExpansion)]))
 (atB : s.locals.lookup (ofString "b")=some (.rStruct [.val (.word secondFee),.val (.word secondExpansion)]))
 (combined : current.toNat+firstExpansion.toNat+secondExpansion.toNat<2^64)
 (run : evaluateHOLFiniteState s (memoryCostTwoAt 6)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615))=
  some (.val (.word (if secondFee=18446744073709551615#64 then 1 else 0))) := by
  simp [evalHOLExact,atB,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_two_6] at run
 rcases memory_cost_pair_guard_returned s post _ _ secondFee secondExpansion (ofString "b") (memoryCostTwoAt 7) value atB cmp run with returned|⟨_,tailRun⟩
 · exact ⟨secondFee,secondExpansion,returned,by omega⟩
 · rw [source_memory_cost_two_7,evaluateHOLFiniteState_return] at tailRun
   have returned : value=.rStruct [.val (.word (firstFee+secondFee)),.val (.word (firstExpansion+secondExpansion))] := by
    simpa [evalHOLExact,evalListHOLExact,atA,atB,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL] using (Prod.mk.inj tailRun).1.symm
   refine ⟨firstFee+secondFee,firstExpansion+secondExpansion,returned,?_⟩
   rw [BitVec.toNat_add_of_lt (by omega)]
   omega
#print axioms memory_cost_two_tail_expansion
end InitECandidate.Runtime
