import InitECandidate.Runtime.HtabRegions
import InitECandidate.Runtime.ScratchAllocationSuccess

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- General `scratch_alloc` decCall contract on a successful allocation: only
the shared `scratch_alloc` lookup is required, so it applies to candidate code
maps whose other entries differ. -/
theorem scratch_alloc_decCall_success {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (sizeArgument : ExpHOL 64) (continuation : ProgHOL 64)
    (pointer size frame : BitVec 64) (v : ValueHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [sizeArgument] = some [.val (.word size)])
    (installed : s.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (within : frame ≤ scratchAllocationEnd pointer size)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc")
      [sizeArgument] continuation) = (some (.returned v),post)) :
    ∃ r inner : PanSemStateFiniteExact 64 F,
      r.locals.lookup name = some (.val (.word (scratchAllocationEnd pointer size))) ∧
      (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) ∧
      r.memory = s.memory ∧ r.memaddrs = s.memaddrs ∧ r.be = s.be ∧
      r.code = s.code ∧
      r.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer size))) s).globals ∧
      size ≤ pointer - frame ∧ frame ≤ scratchAllocationEnd pointer size ∧
      evaluateHOLFiniteState r continuation = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧
      post.be = inner.be ∧ post.code = inner.code := by
  obtain ⟨values,body,callee,rs,w,bodyPost,resumed,inner,argsR,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,
    rh,ragree,rrun,pm,pa,pb,pc⟩ := decCall_returned_globals run
  rw [args] at argsR
  cases argsR
  rw [pan_single_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))) = entry at bodyRun rclk
  have eS : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)) := by
    rw [← hentry]; exact scratchGlobal
  have eF : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [← hentry]; exact frameGlobal
  have eN : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post2,run2,g2,_,m2,c2,a2,_,b2,glob2⟩ :=
    evaluate_source_scratch_alloc_success entry pointer size frame eS eN eF request within
  rw [bodyRun] at run2
  obtain ⟨hres,rfl⟩ := Prod.mk.inj run2
  have hw : w = .val (.word (scratchAllocationEnd pointer size)) :=
    PanSemResultExact.returned.inj (Option.some.inj hres)
  subst hw
  refine ⟨resumed,inner,rh,ragree,rm.trans (m2.trans (by rw [← hentry]; rfl)),
    ra.trans (a2.trans (by rw [← hentry]; rfl)),
    rb.trans (b2.trans (by rw [← hentry]; rfl)),
    rc.trans (c2.trans (by rw [← hentry]; rfl)),?_,request,within,rrun,pm,pa,pb,pc⟩
  · rw [rg,glob2,← hentry]; rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.scratch_alloc_decCall_success
