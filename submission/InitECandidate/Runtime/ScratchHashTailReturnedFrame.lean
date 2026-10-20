import InitECandidate.Runtime.ScratchHashBuilderStores
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem globals_overwrite (globals : HolFiniteMapExact MlS (ValueHOL 64)) (key : MlS) (a b : ValueHOL 64) :
 (globals.update (key,a)).update (key,b)=globals.update (key,b) := by
 apply HolFiniteMapExact.ext
 funext name
 by_cases same : key=name <;>simp [HolFiniteMapExact.lookup_update,FUPDATE,same]

/-- Complete original fixed hash-builder allocation/store tail. The only
possible changes at or above its entry frontier are the five actual pointer
fields of its already allocated header. Every allocation guard and zeroing
step is derived from the same actual returned original execution. -/
theorem scratch_hash_tail_20_4_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (table frame pointer watched : BitVec 64) (value : ValueHOL 64)
 (valid : ScratchHashBuilderContext s table frame pointer)
 (cap : pointer.toNat≤33806089496) (above : pointer.toNat≤watched.toNat)
 (separate : ∀offset∈([32,40,48,56,64] : List (BitVec 64)),watched≠table+offset)
 (run : evaluateHOLFiniteState s (scratchHashAt 6)=(some (.returned value),post)) :
 ∃keys vals used order orderPos : BitVec 64,value=.val (.word table) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word orderPos)) ∧
 frame.toNat≤orderPos.toNat ∧orderPos.toNat+32≤order.toNat ∧order.toNat+32≤used.toNat ∧
 used.toNat+4≤vals.toNat ∧vals.toNat+32≤keys.toNat ∧keys.toNat+96≤pointer.toNat ∧
 post.memory watched=s.memory watched := by
 classical
 rw [source_scratch_hash_6] at run
 have args1 : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [scratchHashSizeExpression (.var .local (ofString "stride"))]=some [.val (.word (96#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,scratchHashSizeExpression,valid.atCap,valid.atStride,panOpHOL,valueIsWord,valueWord]
 obtain ⟨r1,o1,run1,scope1,ctx1,local1,memory1,domain1,endian1,globals1,extent1⟩:=
  valid.allocate_returned post (ofString "keys") _ (scratchHashAt 7) 96 value
   (by decide) (by decide) (by decide) args1 run
 let p1:=scratchAllocationEnd pointer 96
 change ScratchHashBuilderContext r1 table frame p1 at ctx1
 change r1.locals.lookup (ofString "keys")=some (.val (.word p1)) at local1
 change p1.toNat+96≤pointer.toNat at extent1
 have m1 : r1.memory watched=s.memory watched:= (congrFun memory1 watched).trans rfl
 have g1 : r1.globals=s.globals.update (ofString "scratch_ptr",.val (.word p1)):=globals1
 rw [source_scratch_hash_7] at run1
 have nextRun1:=ctx1.store_returned o1 32 p1 (.var .local (ofString "keys")) (scratchHashAt 8) value local1 run1
 let w1:=sourceWriteWord r1 (table+32) p1
 have wctx1:=ctx1.after_context w1 rfl rfl rfl
 have wmem1 : w1.memory watched=s.memory watched := by
  have ne:=separate 32 (by simp)
  change watched≠table+32#64 at ne
  simpa [w1,sourceWriteWord,ne] using m1
 have wglob1 : w1.globals=s.globals.update (ofString "scratch_ptr",.val (.word p1)):=g1
 rw [source_scratch_hash_8] at nextRun1
 have args2 : evalListHOLFinite w1 (h:=fun a=>Classical.propDecidable (w1.memaddrs a)) [scratchHashSizeExpression (.const 8)]=some [.val (.word (32#64))] := by
  simpa using wctx1.fixed_size_arguments (8#64)
 obtain ⟨r2,o2,run2,scope2,ctx2,local2,memory2,domain2,endian2,globals2,extent2⟩:=
  wctx1.allocate_returned o1 (ofString "vals") _ (scratchHashAt 9) 32 value
   (by decide) (by decide) (by decide) args2 nextRun1
 let p2:=scratchAllocationEnd p1 32
 change ScratchHashBuilderContext r2 table frame p2 at ctx2
 change r2.locals.lookup (ofString "vals")=some (.val (.word p2)) at local2
 change p2.toNat+32≤p1.toNat at extent2
 have m2 : r2.memory watched=s.memory watched:= (congrFun memory2 watched).trans wmem1
 have g2 : r2.globals=s.globals.update (ofString "scratch_ptr",.val (.word p2)) := by
  rw [globals2,wglob1]
  exact globals_overwrite _ _ _ _
 rw [source_scratch_hash_9] at run2
 have nextRun2:=ctx2.store_returned o2 40 p2 (.var .local (ofString "vals")) (scratchHashAt 10) value local2 run2
 let w2:=sourceWriteWord r2 (table+40) p2
 have wctx2:=ctx2.after_context w2 rfl rfl rfl
 have wmem2 : w2.memory watched=s.memory watched := by
  have ne:=separate 40 (by simp)
  change watched≠table+40#64 at ne
  simpa [w2,sourceWriteWord,ne] using m2
 have wglob2 : w2.globals=s.globals.update (ofString "scratch_ptr",.val (.word p2)):=g2
 rw [source_scratch_hash_10] at nextRun2
 have args3 : evalListHOLFinite w2 (h:=fun a=>Classical.propDecidable (w2.memaddrs a)) [.var .local (ofString "cap")]=some [.val (.word (4#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,scratchHashSizeExpression,wctx2.atCap,wctx2.atStride,panOpHOL,valueIsWord,valueWord]
 obtain ⟨r3,o3,run3,scope3,ctx3,local3,memory3,domain3,endian3,globals3,extent3⟩:=
  wctx2.allocate_returned o2 (ofString "used") _ (scratchHashAt 11) 4 value
   (by decide) (by decide) (by decide) args3 nextRun2
 let p3:=scratchAllocationEnd p2 4
 change ScratchHashBuilderContext r3 table frame p3 at ctx3
 change r3.locals.lookup (ofString "used")=some (.val (.word p3)) at local3
 change p3.toNat+4≤p2.toNat at extent3
 have m3 : r3.memory watched=s.memory watched:= (congrFun memory3 watched).trans wmem2
 have g3 : r3.globals=s.globals.update (ofString "scratch_ptr",.val (.word p3)) := by
  rw [globals3,wglob2]
  exact globals_overwrite _ _ _ _
 rw [source_scratch_hash_11] at run3
 obtain ⟨zero,zeroRun,zeroTail⟩:=encode_header_seq_returned_of_no_return r3 o3 _ _ value
  (fun v=>(evaluate_handlerFree_call_control r3 _ _ _).2.2 v) run3
 have zeroArgs : evalListHOLFinite r3 (h:=fun a=>Classical.propDecidable (r3.memaddrs a))
  [.var .local (ofString "used"),.var .local (ofString "cap")]=some [.val (.word p3),.val (.word (4#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,local3,ctx3.atCap]
 have usedCap : p3.toNat+4≤33806089496 := by omega
 have outside : p3.toNat+4≤watched.toNat := by omega
 obtain ⟨zeroFrame,zeroLocals⟩:=memzero_call_normal_memory r3 zero _ p3 4 watched zeroArgs ctx3.code
  (scratchAllocationEnd_mask_aligned p2 4) usedCap (Or.inr outside) zeroRun
 have zeroGlobals:=(memzero_call_globals_frame [.var .local (ofString "used"),.var .local (ofString "cap")]) r3 ctx3.code
 have zeroMetadata:=evaluateHOLFiniteState_metadata r3 (.call (some (none,none)) (ofString "memzero")
  [.var .local (ofString "used"),.var .local (ofString "cap")])
 rw [zeroRun] at zeroGlobals zeroMetadata
 have zeroCtx:=ctx3.after_context zero zeroLocals zeroGlobals zeroMetadata.1
 have usedLocal : zero.locals.lookup (ofString "used")=some (.val (.word p3)) := by rw [zeroLocals];exact local3
 rw [source_scratch_hash_12] at zeroTail
 have nextRun3:=zeroCtx.store_returned o3 48 p3 (.var .local (ofString "used")) (scratchHashAt 13) value usedLocal zeroTail
 let w3:=sourceWriteWord zero (table+48) p3
 have wctx3:=zeroCtx.after_context w3 rfl rfl rfl
 have wmem3 : w3.memory watched=s.memory watched := by
  have ne:=separate 48 (by simp)
  change watched≠table+48#64 at ne
  simpa [w3,sourceWriteWord,ne] using zeroFrame.trans m3
 have wglob3 : w3.globals=s.globals.update (ofString "scratch_ptr",.val (.word p3)):=zeroGlobals.trans g3
 rw [source_scratch_hash_13] at nextRun3
 have args4 : evalListHOLFinite w3 (h:=fun a=>Classical.propDecidable (w3.memaddrs a)) [scratchHashSizeExpression (.const 8)]=some [.val (.word (32#64))] := by
  simpa using wctx3.fixed_size_arguments (8#64)
 obtain ⟨r4,o4,run4,scope4,ctx4,local4,memory4,domain4,endian4,globals4,extent4⟩:=
  wctx3.allocate_returned o3 (ofString "order") _ (scratchHashAt 14) 32 value
   (by decide) (by decide) (by decide) args4 nextRun3
 let p4:=scratchAllocationEnd p3 32
 change ScratchHashBuilderContext r4 table frame p4 at ctx4
 change r4.locals.lookup (ofString "order")=some (.val (.word p4)) at local4
 change p4.toNat+32≤p3.toNat at extent4
 have m4 : r4.memory watched=s.memory watched:= (congrFun memory4 watched).trans wmem3
 have g4 : r4.globals=s.globals.update (ofString "scratch_ptr",.val (.word p4)) := by
  rw [globals4,wglob3]
  exact globals_overwrite _ _ _ _
 rw [source_scratch_hash_14] at run4
 have nextRun4:=ctx4.store_returned o4 56 p4 (.var .local (ofString "order")) (scratchHashAt 15) value local4 run4
 let w4:=sourceWriteWord r4 (table+56) p4
 have wctx4:=ctx4.after_context w4 rfl rfl rfl
 have wmem4 : w4.memory watched=s.memory watched := by
  have ne:=separate 56 (by simp)
  change watched≠table+56#64 at ne
  simpa [w4,sourceWriteWord,ne] using m4
 have wglob4 : w4.globals=s.globals.update (ofString "scratch_ptr",.val (.word p4)):=g4
 rw [source_scratch_hash_15] at nextRun4
 have args5 : evalListHOLFinite w4 (h:=fun a=>Classical.propDecidable (w4.memaddrs a)) [scratchHashSizeExpression (.const 8)]=some [.val (.word (32#64))] := by
  simpa using wctx4.fixed_size_arguments (8#64)
 obtain ⟨r5,o5,run5,scope5,ctx5,local5,memory5,domain5,endian5,globals5,extent5⟩:=
  wctx4.allocate_returned o4 (ofString "order_pos") _ (scratchHashAt 16) 32 value
   (by decide) (by decide) (by decide) args5 nextRun4
 let p5:=scratchAllocationEnd p4 32
 change ScratchHashBuilderContext r5 table frame p5 at ctx5
 change r5.locals.lookup (ofString "order_pos")=some (.val (.word p5)) at local5
 change p5.toNat+32≤p4.toNat at extent5
 have m5 : r5.memory watched=s.memory watched:= (congrFun memory5 watched).trans wmem4
 have g5 : r5.globals=s.globals.update (ofString "scratch_ptr",.val (.word p5)) := by
  rw [globals5,wglob4]
  exact globals_overwrite _ _ _ _
 rw [source_scratch_hash_16] at run5
 have nextRun5:=ctx5.store_returned o5 64 p5 (.var .local (ofString "order_pos")) (scratchHashAt 17) value local5 run5
 let w5:=sourceWriteWord r5 (table+64) p5
 have wctx5:=ctx5.after_context w5 rfl rfl rfl
 have wmem5 : w5.memory watched=s.memory watched := by
  have ne:=separate 64 (by simp)
  change watched≠table+64#64 at ne
  simpa [w5,sourceWriteWord,ne] using m5
 have wglob5 : w5.globals=s.globals.update (ofString "scratch_ptr",.val (.word p5)):=g5
 have returned : evaluateHOLFiniteState w5 (scratchHashAt 17)=
  (some (.returned (.val (.word table))),emptyLocalsHOLFinite w5) := by
  rw [source_scratch_hash_17]
  simp [evaluateHOLFiniteState_return,evalHOLExact,wctx5.atTable,shapeOfHOLExact]
 obtain ⟨resultEq,postEq⟩:=Prod.mk.inj (nextRun5.symm.trans returned)
 have valueEq:=PanSemResultExact.returned.inj (Option.some.inj resultEq)
 refine ⟨p1,p2,p3,p4,p5,valueEq,?_,BitVec.le_def.mp ctx5.ordered,extent5,extent4,extent3,extent2,extent1,?_⟩
 · rw [scope1,scope2,scope3,scope4,scope5,postEq]
   exact wglob5
 · rw [scope1,scope2,scope3,scope4,scope5,postEq]
   exact wmem5
#print axioms scratch_hash_tail_20_4_returned_frame
end InitECandidate.Runtime
