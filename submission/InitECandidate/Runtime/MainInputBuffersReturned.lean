import InitECandidate.Runtime.MainBuffersReturned
import InitECandidate.Runtime.InputBlobDeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's actual input read followed by output-buffer allocation. The copied
input remains below the advanced heap and above the initialized scratch ceiling. -/
theorem main_input_buffers_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (input : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word input)))
    (bounded : input.toNat ≤ 33806089496)
    (above : 2713714688 ≤ input.toNat)
    (run : evaluateHOLFiniteState state (mainAt 14) = (some (.returned value),post)) :
    ∃ (ready output : PanSemStateFiniteExact 64 F) (length out zero nextHeap : BitVec 64),
      evaluateHOLFiniteState ready (mainAt 17) = (some (.returned value),output) ∧
      ready.locals.lookup (ofString "inp") = some (.rStruct [.val (.word input),.val (.word length)]) ∧
      ready.locals.lookup (ofString "out") = some (.val (.word out)) ∧
      ready.locals.lookup (ofString "z32") = some (.val (.word zero)) ∧
      length.toNat ≤ 134217712 ∧ input.toNat + length.toNat < 2 ^ 64 ∧
      input.toNat + length.toNat + 8 ≤ out.toNat ∧ out.toNat + 256 ≤ zero.toNat ∧
      zero.toNat + 32 ≤ nextHeap.toNat ∧ input.toNat + length.toNat ≤ nextHeap.toNat ∧
      out.toNat % 8 = 0 ∧ zero.toNat % 8 = 0 ∧ nextHeap.toNat % 8 = 0 ∧
      nextHeap.toNat ≤ 33806089496 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      (input.toNat + length.toNat ≤ 2701135872 ∨
        2713714688 % 8 = 0 ∧ 2713714688 ≤ input.toNat) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  rw [source_main_input_declaration] at run
  obtain ⟨length,out,middle,midOutput,tail,locals,installed,domain,small,midHeap,midBound,midAligned,
      cover,nowrap,other,postMemory,postGlobals,postDomain⟩ :=
    inputBlob_declaration_returned state post (ofString "inp") (mainAt 15) input value heap bounded code run
  have inp : middle.locals.lookup (ofString "inp") =
      some (.rStruct [.val (.word input),.val (.word length)]) := by
    simp [locals,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨ready,output,zero,nextHeap,rest,retInp,retOut,retZero,retHeap,retBound,retAligned,zeroAligned,
      outCover,zeroCover,inputCover,_,retCode,retDomain,retOther,tailMemory,tailGlobals,tailDomain⟩ :=
    main_buffers_returned middle midOutput out input length value (installed.trans code) midHeap midBound inp (by omega) tail
  refine ⟨ready,output,length,out,zero,nextHeap,rest,retInp,retOut,retZero,small,nowrap,cover,outCover,
    zeroCover,inputCover,midAligned,zeroAligned,retAligned,retBound,retHeap,?_,retCode.trans installed,
    retDomain.trans domain,Or.inr ⟨by decide,above⟩,postMemory.trans tailMemory,
    postGlobals.trans tailGlobals,postDomain.trans tailDomain⟩
  intro key different
  exact (retOther key different).trans (other key different)

#print axioms main_input_buffers_returned
end InitECandidate.Runtime
