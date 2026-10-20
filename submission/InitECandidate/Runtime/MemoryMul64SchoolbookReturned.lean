import InitECandidate.Runtime.FrameNewSource
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.MemoryPrimitiveReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def memoryMul64Schoolbook (a b : BitVec 64) : BitVec 64×BitVec 64 :=
 let a0:=a&&&4294967295#64
 let a1:=a>>>32
 let b0:=b&&&4294967295#64
 let b1:=b>>>32
 let p00:=a0*b0
 let p11:=a1*b1
 let mid:=wordAddCarryHOL (a0*b1) (a1*b0) 0
 let lo:=wordAddCarryHOL p00 (mid.1<<<32) 0
 (lo.1,p11+(mid.1>>>32)+(mid.2<<<32)+lo.2)

def memoryMul64Program : ProgHOL 64 :=
 .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"),.const 4294967295])
 (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const 32))
 (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"),.const 4294967295])
 (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const 32))
 (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b0")])
 (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b1")])
 (.dec (ofString "mid") (.comb [.one,.one]) (.rstruct [.const 0,.const 0])
 (.seq (.primitive (ofString "mid") .addCarry [.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b1")],.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b0")],.const 0])
 (.dec (ofString "lo") (.comb [.one,.one]) (.rstruct [.const 0,.const 0])
 (.seq (.primitive (ofString "lo") .addCarry [.var .local (ofString "p00"),.shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.const 0])
 (.dec (ofString "hi") .one (.op .add [.var .local (ofString "p11"),.shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const 32),.rfield 1 (.var .local (ofString "lo"))])
 (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")),.var .local (ofString "hi")]))))))))))))

theorem source_memory_mul64 : structuralFunctionBody Guest.guestFn_mul64x64=memoryMul64Program := rfl


def memoryMul64At (index : Nat) : ProgHOL 64 := (statelessNext^[index]) memoryMul64Program

/-- Exact returned arithmetic of the original helper, through actual scalar
scopes and both actual add-with-carry primitive updates. -/
theorem memory_mul64_schoolbook_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (a b : BitVec 64) (value : ValueHOL 64)
 (atA : s.locals.lookup (ofString "a")=some (.val (.word a)))
 (atB : s.locals.lookup (ofString "b")=some (.val (.word b)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mul64x64)=(some (.returned value),post)) :
 value=.rStruct [.val (.word (memoryMul64Schoolbook a b).1),.val (.word (memoryMul64Schoolbook a b).2)] := by
 let aa0:=a&&&4294967295#64
 let aa1:=a>>>(32:Nat)
 let bb0:=b&&&4294967295#64
 let bb1:=b>>>(32:Nat)
 let pp00:=aa0*bb0
 let pp11:=aa1*bb1
 let mm:=wordAddCarryHOL (aa0*bb1) (aa1*bb0) (0#64)
 let ll:=wordAddCarryHOL pp00 (mm.1<<<(32:Nat)) (0#64)
 let hh:=pp11+(mm.1>>>(32:Nat))+(mm.2<<<(32:Nat))+ll.2
 have andDef (x y : BitVec 64) : AndOp.and x y=x&&&y := rfl
 rw [sourceFunctionBody_eq_structural,source_memory_mul64] at run
 change evaluateHOLFiniteState s (memoryMul64At 0)=_ at run
 have h0:=run
 have step0 : memoryMul64At 0=.dec (ofString "a0") .one (.op .and [.var .local (ofString "a"),.const 4294967295]) (memoryMul64At 1) := rfl
 rw [step0] at h0
 obtain ⟨v0,o0,e0,h1,scope0⟩:=funding_declaration_returned_context h0
 have eq0 : v0=(.val (.word aa0)) := by
  simpa (config:={decide:=true}) [aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e0.symm
 subst v0
 let u1:=setVarHOLFinite (ofString "a0") (.val (.word aa0)) s
 change evaluateHOLFiniteState u1 (memoryMul64At 1)=_ at h1
 have step1 : memoryMul64At 1=.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const 32)) (memoryMul64At 2) := rfl
 rw [step1] at h1
 obtain ⟨v1,o1,e1,h2,scope1⟩:=funding_declaration_returned_context h1
 have eq1 : v1=(.val (.word aa1)) := by
  simpa (config:={decide:=true}) [u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e1.symm
 subst v1
 let u2:=setVarHOLFinite (ofString "a1") (.val (.word aa1)) u1
 change evaluateHOLFiniteState u2 (memoryMul64At 2)=_ at h2
 have step2 : memoryMul64At 2=.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"),.const 4294967295]) (memoryMul64At 3) := rfl
 rw [step2] at h2
 obtain ⟨v2,o2,e2,h3,scope2⟩:=funding_declaration_returned_context h2
 have eq2 : v2=(.val (.word bb0)) := by
  simpa (config:={decide:=true}) [u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e2.symm
 subst v2
 let u3:=setVarHOLFinite (ofString "b0") (.val (.word bb0)) u2
 change evaluateHOLFiniteState u3 (memoryMul64At 3)=_ at h3
 have step3 : memoryMul64At 3=.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const 32)) (memoryMul64At 4) := rfl
 rw [step3] at h3
 obtain ⟨v3,o3,e3,h4,scope3⟩:=funding_declaration_returned_context h3
 have eq3 : v3=(.val (.word bb1)) := by
  simpa (config:={decide:=true}) [u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e3.symm
 subst v3
 let u4:=setVarHOLFinite (ofString "b1") (.val (.word bb1)) u3
 change evaluateHOLFiniteState u4 (memoryMul64At 4)=_ at h4
 have step4 : memoryMul64At 4=.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b0")]) (memoryMul64At 5) := rfl
 rw [step4] at h4
 obtain ⟨v4,o4,e4,h5,scope4⟩:=funding_declaration_returned_context h4
 have eq4 : v4=(.val (.word pp00)) := by
  simpa (config:={decide:=true}) [u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e4.symm
 subst v4
 let u5:=setVarHOLFinite (ofString "p00") (.val (.word pp00)) u4
 change evaluateHOLFiniteState u5 (memoryMul64At 5)=_ at h5
 have step5 : memoryMul64At 5=.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b1")]) (memoryMul64At 6) := rfl
 rw [step5] at h5
 obtain ⟨v5,o5,e5,h6,scope5⟩:=funding_declaration_returned_context h5
 have eq5 : v5=(.val (.word pp11)) := by
  simpa (config:={decide:=true}) [u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e5.symm
 subst v5
 let u6:=setVarHOLFinite (ofString "p11") (.val (.word pp11)) u5
 change evaluateHOLFiniteState u6 (memoryMul64At 6)=_ at h6
 have step6 : memoryMul64At 6=.dec (ofString "mid") (.comb [.one,.one]) (.rstruct [.const 0,.const 0]) (memoryMul64At 7) := rfl
 rw [step6] at h6
 obtain ⟨v6,o6,e6,h7,scope6⟩:=funding_declaration_returned_context h6
 have eq6 : v6=(.rStruct [.val (.word (0#64)),.val (.word (0#64))]) := by
  simpa (config:={decide:=true}) [u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e6.symm
 subst v6
 let u7:=setVarHOLFinite (ofString "mid") (.rStruct [.val (.word (0#64)),.val (.word (0#64))]) u6
 change evaluateHOLFiniteState u7 (memoryMul64At 7)=_ at h7
 have step7 : memoryMul64At 7=.seq (.primitive (ofString "mid") .addCarry [.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b1")],.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b0")],.const 0]) (memoryMul64At 8) := rfl
 rw [step7] at h7
 have args7 : evalListHOLFinite u7 (h:=fun x=>Classical.propDecidable (u7.memaddrs x)) [.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b1")],.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b0")],.const 0]=some [.val (.word (aa0*bb1)),.val (.word (aa1*bb0)),.val (.word (0#64))] := by
  simp (config:={decide:=true}) [u7,u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc]
 have prim7 : panPrimopHOLExact .addCarry [.val (.word (aa0*bb1)),.val (.word (aa1*bb0)),.val (.word (0#64))]=some (.rStruct [.val (.word mm.1),.val (.word mm.2)]) := by simp [panPrimopHOLExact,mm]
 have h8:=memory_primitive_returned_context u7 o6 (ofString "mid") .addCarry [.panop .mul [.var .local (ofString "a0"),.var .local (ofString "b1")],.panop .mul [.var .local (ofString "a1"),.var .local (ofString "b0")],.const 0] [.val (.word (aa0*bb1)),.val (.word (aa1*bb0)),.val (.word (0#64))] (.rStruct [.val (.word mm.1),.val (.word mm.2)]) value (memoryMul64At 8) args7 prim7 h7
 let u8:=setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mm.1),.val (.word mm.2)]) u7
 change evaluateHOLFiniteState u8 (memoryMul64At 8)=_ at h8
 have step8 : memoryMul64At 8=.dec (ofString "lo") (.comb [.one,.one]) (.rstruct [.const 0,.const 0]) (memoryMul64At 9) := rfl
 rw [step8] at h8
 obtain ⟨v8,o8,e8,h9,scope8⟩:=funding_declaration_returned_context h8
 have eq8 : v8=(.rStruct [.val (.word (0#64)),.val (.word (0#64))]) := by
  simpa (config:={decide:=true}) [u8,u7,u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e8.symm
 subst v8
 let u9:=setVarHOLFinite (ofString "lo") (.rStruct [.val (.word (0#64)),.val (.word (0#64))]) u8
 change evaluateHOLFiniteState u9 (memoryMul64At 9)=_ at h9
 have step9 : memoryMul64At 9=.seq (.primitive (ofString "lo") .addCarry [.var .local (ofString "p00"),.shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.const 0]) (memoryMul64At 10) := rfl
 rw [step9] at h9
 have args9 : evalListHOLFinite u9 (h:=fun x=>Classical.propDecidable (u9.memaddrs x)) [.var .local (ofString "p00"),.shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.const 0]=some [.val (.word pp00),.val (.word (mm.1<<<(32:Nat))),.val (.word (0#64))] := by
  simp (config:={decide:=true}) [u9,u8,u7,u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc]
 have prim9 : panPrimopHOLExact .addCarry [.val (.word pp00),.val (.word (mm.1<<<(32:Nat))),.val (.word (0#64))]=some (.rStruct [.val (.word ll.1),.val (.word ll.2)]) := by simp [panPrimopHOLExact,ll]
 have h10:=memory_primitive_returned_context u9 o8 (ofString "lo") .addCarry [.var .local (ofString "p00"),.shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.const 0] [.val (.word pp00),.val (.word (mm.1<<<(32:Nat))),.val (.word (0#64))] (.rStruct [.val (.word ll.1),.val (.word ll.2)]) value (memoryMul64At 10) args9 prim9 h9
 let u10:=setVarHOLFinite (ofString "lo") (.rStruct [.val (.word ll.1),.val (.word ll.2)]) u9
 change evaluateHOLFiniteState u10 (memoryMul64At 10)=_ at h10
 have step10 : memoryMul64At 10=.dec (ofString "hi") .one (.op .add [.var .local (ofString "p11"),.shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const 32),.shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const 32),.rfield 1 (.var .local (ofString "lo"))]) (memoryMul64At 11) := rfl
 rw [step10] at h10
 obtain ⟨v10,o10,e10,h11,scope10⟩:=funding_declaration_returned_context h10
 have eq10 : v10=(.val (.word hh)) := by
  simpa (config:={decide:=true}) [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc] using e10.symm
 subst v10
 let u11:=setVarHOLFinite (ofString "hi") (.val (.word hh)) u10
 change evaluateHOLFiniteState u11 (memoryMul64At 11)=_ at h11
 have finalStep : memoryMul64At 11=.return (.rstruct [.rfield 0 (.var .local (ofString "lo")),.var .local (ofString "hi")]) := rfl
 rw [finalStep] at h11
 have finalEval : @evalHOLExact 64 F _ u11.toExact (fun x=>Classical.propDecidable (u11.memaddrs x))
  (.rstruct [.rfield 0 (.var .local (ofString "lo")),.var .local (ofString "hi")])=
  some (.rStruct [.val (.word ll.1),.val (.word hh)]) := by
  simp (config:={decide:=true}) [u11,u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,aa0,aa1,bb0,bb1,pp00,pp11,hh,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,evalListHOLFinite,atA,atB,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,valueIsWord,valueWord,andDef,BitVec.add_assoc]
 have returnRun : evaluateHOLFiniteState u11 (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")),.var .local (ofString "hi")]))=
  (some (.returned (.rStruct [.val (.word ll.1),.val (.word hh)])),emptyLocalsHOLFinite u11) := by
  rw [evaluateHOLFiniteState_return,finalEval]
  simp [shapeOfHOLExact,sizeOfShapeWithContextHOL]
 have returned:=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (h11.symm.trans returnRun)).1)

 simpa [memoryMul64Schoolbook,aa0,aa1,bb0,bb1,pp00,pp11,mm,ll,hh] using returned
#print axioms memory_mul64_schoolbook_returned
end InitECandidate.Runtime
