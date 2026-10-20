import InitECandidate.Runtime.EvmOperandStackGrowthSource
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def stackPushGrownCapacity (capacity : BitVec 64) : BitVec 64 :=
 if 1024 < capacity.toNat*2 then 1024#64 else capacity*2#64

theorem stack_push_grown_capacity_bounds (capacity : BitVec 64)
 (positive : 1≤capacity.toNat) (small : capacity.toNat<1024) :
 capacity.toNat+1≤(stackPushGrownCapacity capacity).toNat ∧
 (stackPushGrownCapacity capacity).toNat≤1024 := by
 have twice : (capacity*2#64).toNat=capacity.toNat*2 := by
  rw [BitVec.toNat_mul_of_lt (by change capacity.toNat*2<2^64;omega)];rfl
 unfold stackPushGrownCapacity
 split
 · change capacity.toNat+1≤1024 ∧1024≤1024;omega
 · rw [twice];omega

/-- The real source capacity clamp chooses exactly min(2*capacity,1024),
with no assumed continuation execution or assignment validity. -/
theorem stack_push_capacity_clamp_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (capacity : BitVec 64) (small : capacity.toNat<1024)
 (atCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word (capacity*2))))
 (run : evaluateHOLFiniteState s (stackPushGrowthAt 2)=(none,post)) :
 ∃ ready : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (stackPushGrowthAt 3)=(none,post) ∧
 ready.locals.lookup (ofString "ncap")=some (.val (.word (stackPushGrownCapacity capacity))) ∧
 ready.memory=s.memory ∧ready.globals=s.globals ∧ready.clock=s.clock ∧
 ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧ready.code=s.code ∧
 (∀key,key≠ofString "ncap" → ready.locals.lookup key=s.locals.lookup key) := by
 have twice : (capacity*2#64).toNat=capacity.toNat*2 := by
  rw [BitVec.toNat_mul_of_lt (by change capacity.toNat*2<2^64;omega)];rfl
 rw [source_stack_push_growth_2] at run
 obtain ⟨ready,clampRun,tailRun⟩:=encode_header_seq_normal s post _ _ run
 by_cases large : 1024<capacity.toNat*2
 · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.const 1024) (.var .local (ofString "ncap")))=some (.val (.word 1)) := by
    simp [evalHOLExact,atCapacity,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,twice,large]
   rw [evaluateHOLFiniteState_ite,cmp] at clampRun
   change evaluateHOLFiniteState s (.assign .local (ofString "ncap") (.const 1024))=(none,ready) at clampRun
   rw [evaluateHOLFiniteState_assign] at clampRun
   dsimp only [evalHOLExact] at clampRun
   split at clampRun
   · have equal : ready=setKvarHOLFinite .local (ofString "ncap") (.val (.word 1024)) s := (Prod.mk.inj clampRun).2.symm
     subst ready
     refine ⟨_,tailRun,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
     · simp [stackPushGrownCapacity,large,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
     · intro key different
       simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
   · simp at clampRun
 · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.const 1024) (.var .local (ofString "ncap")))=some (.val (.word 0)) := by
    simp [evalHOLExact,atCapacity,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,twice,large]
   rw [evaluateHOLFiniteState_ite,cmp] at clampRun
   change evaluateHOLFiniteState s .skip=(none,ready) at clampRun
   rw [evaluateHOLFiniteState_skip] at clampRun
   have equal : ready=s := (Prod.mk.inj clampRun).2.symm
   subst ready
   refine ⟨s,tailRun,?_,rfl,rfl,rfl,rfl,rfl,rfl,by intros;rfl⟩
   simpa [stackPushGrownCapacity,large] using atCapacity
#print axioms stack_push_grown_capacity_bounds
#print axioms stack_push_capacity_clamp_normal
end InitECandidate.Runtime
