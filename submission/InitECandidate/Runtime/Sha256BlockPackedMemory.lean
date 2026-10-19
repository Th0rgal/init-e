import InitECandidate.Runtime.Sha256PackLoopFacts
import InitECandidate.Runtime.Sha256BlockExternalMemory
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockPack_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index pointer accelerator watched : BitVec 64) (value : ValueHOL 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (small : index.toNat ≤ 4) (aligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaBlockAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaBlock_pack] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  obtain ⟨frame,accel,installed,nextIndex,indexLocal,_⟩ := shaBlockPack_loop_normal_facts state middle index accelerator watched
    atIndex atAccel small accelFits accelOutside code normal
  have kept := evaluate_avoidsLocal_flowing (ofString "stp")
    (.while (.cmp .less (.var .local (ofString "i")) (.const 4)) shaBlockPackBody) (by decide) state
    (by rw [normal]; exact Or.inl rfl)
  rw [normal] at kept
  exact (shaBlockExternal_suffix_returned_memory middle post nextIndex pointer accelerator watched value indexLocal
    (kept.trans atPointer) accel aligned accelFits pointerFits accelOutside pointerOutside installed tail).trans frame

theorem shaBlockCounter_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (aligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaBlockAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaBlock_counter] at run
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0)
    (0 : BitVec 64) (shaBlockAt 2) (some (.returned value)) rfl run
  have framed := shaBlockPack_suffix_returned_memory
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) inner 0 pointer accelerator watched value
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer)
    atAccel (by decide) aligned accelFits pointerFits accelOutside pointerOutside code bodyRun
  rw [scope]
  exact framed

#print axioms shaBlockPack_suffix_returned_memory
#print axioms shaBlockCounter_suffix_returned_memory
end InitECandidate.Runtime
