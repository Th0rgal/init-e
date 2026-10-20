import InitECandidate.Runtime.MemoryWordsOfDeclarationReturned
import InitECandidate.Runtime.MemoryMul64SquareDeclaration
import InitECandidate.Runtime.MemoryMul64SquareCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def memoryGasCostAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_memory_gas_cost)

theorem source_memory_gas_cost_0 : memoryGasCostAt 0=.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "size")] (memoryGasCostAt 1) := rfl
theorem source_memory_gas_cost_1 : memoryGasCostAt 1=.decCall (ofString "sq") (.comb [.one,.one]) (ofString "mul64x64") [.var .local (ofString "w"),.var .local (ofString "w")] (memoryGasCostAt 2) := rfl
theorem source_memory_gas_cost_2 : memoryGasCostAt 2=.seq
 (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0)) (.return (.const 18446744073709551615)) .skip) (memoryGasCostAt 3) := rfl

/-- Actual memory_gas_cost either saturates or its real input size is safely
below the 64-bit clamp-wrap region. The original schoolbook multiply and
both real addCarry operations are proved, not assumed correct. -/
theorem memory_gas_cost_returned_size_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (size : BitVec 64) (value : ValueHOL 64)
 (atSize : s.locals.lookup (ofString "size")=some (.val (.word size)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_memory_gas_cost)=(some (.returned value),post)) :
 value=.val (.word (18446744073709551615#64)) ∨size.toNat<2^37 := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryGasCostAt 0)=_ at run
 rw [source_memory_gas_cost_0] at run
 have args0 : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "size")]=some [.val (.word size)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atSize]
 obtain ⟨words,firstPost,firstOutput,firstRun,firstScope,lower,ceiling,_,_,firstCode,_,_⟩:=
  memory_words_of_declaration_returned s post (ofString "w") _ (memoryGasCostAt 1) size value args0 code run
 let first:=setVarHOLFinite (ofString "w") (.val (.word words)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryGasCostAt 1)=_ at firstRun
 have w : first.locals.lookup (ofString "w")=some (.val (.word words)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have args1 : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.var .local (ofString "w"),.var .local (ofString "w")]=some [.val (.word words),.val (.word words)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,w]
 rw [source_memory_gas_cost_1] at firstRun
 obtain ⟨secondPost,secondOutput,secondRun,secondScope,_,_,_,_,_⟩:=
  memory_mul64_square_declaration_returned first firstOutput (ofString "sq") _ (memoryGasCostAt 2) words value args1 (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "sq") (.rStruct [.val (.word (memoryMul64Schoolbook words words).1),.val (.word (memoryMul64Schoolbook words words).2)]) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryGasCostAt 2)=_ at secondRun
 have sq : second.locals.lookup (ofString "sq")=some (.rStruct [.val (.word (memoryMul64Schoolbook words words).1),.val (.word (memoryMul64Schoolbook words words).2)]) := by
  simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 by_cases zero : (memoryMul64Schoolbook words words).2=0#64
 · right
   have bounded:=memory_mul64_square_high_zero_ceiling words ceiling zero
   omega
 · left
   have cmp : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a))
    (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0))=some (.val (.word 1)) := by
    simp [evalHOLExact,sq,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
   have direct : evaluateHOLFiniteState second (memoryGasCostAt 2)=
    (some (.returned (.val (.word (18446744073709551615#64)))),emptyLocalsHOLFinite second) := by
    rw [source_memory_gas_cost_2,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
   exact PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (secondRun.symm.trans direct)).1)
#print axioms memory_gas_cost_returned_size_ceiling
end InitECandidate.Runtime
