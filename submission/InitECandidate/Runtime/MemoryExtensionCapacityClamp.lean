import InitECandidate.Runtime.MemoryExtensionCapacityGeometry
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual original growth clamp chooses the real doubled or padded
capacity, extracting assignment validity from its normal execution. -/
theorem memory_extension_capacity_clamp_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (capacity newLength : BitVec 64)
 (atCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word (capacity*2#64))))
 (atLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (run : evaluateHOLFiniteState s (memoryExtensionGrowthAt 1)=(none,post)) :
 ∃ ready : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (memoryExtensionGrowthAt 2)=(none,post) ∧
 ready.locals.lookup (ofString "ncap")=some (.val (.word (memoryExtensionCapacity capacity newLength))) ∧
 ready.memory=s.memory ∧ready.globals=s.globals ∧ready.clock=s.clock ∧
 ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧ready.code=s.code ∧
 (∀key,key≠ofString "ncap" → ready.locals.lookup key=s.locals.lookup key) := by
 rw [source_memory_extension_growth_1] at run
 obtain ⟨ready,clampRun,tailRun⟩:=encode_header_seq_normal s post _ _ run
 by_cases larger : (capacity*2#64).toNat<newLength.toNat
 · have normalized:=larger
   simp only [BitVec.toNat_mul] at normalized
   change capacity.toNat*2%18446744073709551616<newLength.toNat at normalized
   have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))=some (.val (.word 1)) := by
    simp [evalHOLExact,atCapacity,atLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,larger,normalized]
   rw [evaluateHOLFiniteState_ite,cmp] at clampRun
   change evaluateHOLFiniteState s (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"),.const 1024]))=(none,ready) at clampRun
   have assigned : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.op .add [.var .local (ofString "nlen"),.const 1024])=some (.val (.word (newLength+1024#64))) := by
    simp [evalHOLExact,evalListHOLExact,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
   rw [evaluateHOLFiniteState_assign,assigned] at clampRun
   dsimp only at clampRun
   split at clampRun
   · have equal : ready=setKvarHOLFinite .local (ofString "ncap") (.val (.word (newLength+1024#64))) s := (Prod.mk.inj clampRun).2.symm
     subst ready
     refine ⟨_,tailRun,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
     · simp [memoryExtensionCapacity,larger,normalized,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
     · intro key different
       simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
   · simp at clampRun
 · have normalized:=larger
   simp only [BitVec.toNat_mul] at normalized
   change ¬capacity.toNat*2%18446744073709551616<newLength.toNat at normalized
   have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))=some (.val (.word 0)) := by
    simp [evalHOLExact,atCapacity,atLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,larger,normalized]
   rw [evaluateHOLFiniteState_ite,cmp] at clampRun
   change evaluateHOLFiniteState s .skip=(none,ready) at clampRun
   rw [evaluateHOLFiniteState_skip] at clampRun
   have equal : ready=s := (Prod.mk.inj clampRun).2.symm
   subst ready
   refine ⟨s,tailRun,?_,rfl,rfl,rfl,rfl,rfl,rfl,by intros;rfl⟩
   simpa [memoryExtensionCapacity,larger,normalized] using atCapacity
#print axioms memory_extension_capacity_clamp_normal
end InitECandidate.Runtime
