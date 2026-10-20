import InitECandidate.Runtime.MsgNewDeclarationReach
import InitECandidate.Runtime.HashNewMemoryBeforeHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Concrete scalar writes to the first 72 message bytes retain the derived
allocation geometry and every older word. The address is mapped by the actual
message extent and arena domain, not by a successful-store premise. -/
theorem msg_new_ready_store_reaches {F : Type} (base mid : PanSemStateFiniteExact 64 F)
 (pointer offset word : BitVec 64) (expression : ExpHOL 64) (tail : ProgHOL 64)
 (ctx : MsgNewReady base pointer mid) (inside : offset.toNat<72)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→base.memaddrs a)
 (value : @evalHOLExact 64 F _ mid.toExact (fun a=>Classical.propDecidable (mid.memaddrs a)) expression=some (.val (.word word))) :
 Reaches mid (.seq (.store (.op .add [.var .local (ofString "m"),.const offset]) expression) tail)
  (MsgNewReady base pointer) 0 tail := by
 have header : pointer.toNat+72≤33806089496 := by have extent:=ctx.extent;have cap:=ctx.capped;omega
 have natural : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by omega)
 have readable : mid.memaddrs (pointer+offset) := by rw [ctx.domain];exact domain _ (by rw [natural];omega)
 have address : @evalHOLExact 64 F _ mid.toExact (fun a=>Classical.propDecidable (mid.memaddrs a))
  (.op .add [.var .local (ofString "m"),.const offset])=some (.val (.word (pointer+offset))) := by
  simp [evalHOLExact,evalListHOLExact,ctx.atMessage,wordOpHOL,wordOp,valueIsWord,valueWord]
 let next:=sourceWriteWord mid (pointer+offset) word
 have run:=evaluate_store_word mid (pointer+offset) word _ _ address value readable
 have ready : MsgNewReady base pointer next := by
  refine ⟨ctx.atMessage,ctx.locals,ctx.code,ctx.domain,ctx.globals,ctx.extent,ctx.aligned,ctx.capped,?_⟩
  intro watched before
  exact (sourceWriteWord_before_header mid pointer watched word offset header inside before).trans (ctx.memory watched before)
 exact reaches_seq mid _ tail 0 (MsgNewReady base pointer)
  (Or.inl ⟨next,ready,by simp [next,sourceWriteWord],by simp [next,sourceWriteWord],run⟩)
#print axioms msg_new_ready_store_reaches
end InitECandidate.Runtime
