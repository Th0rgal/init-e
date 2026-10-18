import InitECandidate.Runtime.WordStorePlanMemory
import InitECandidate.Runtime.Sha256GlobalsFrame
import InitECandidate.Runtime.AllocationSeparation
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def shaStateInitStores : List (Nat × BitVec 64) :=
  [(0,1779033703),(8,3144134277),(16,1013904242),(24,2773480762),
   (32,1359893119),(40,2600822924),(48,528734635),(56,1541459225)]

theorem source_shaStateInit_stores : sourceFunctionBody Guest.guestFn_sha256_state_init =
    wordStorePlan (ofString "stp") shaStateInitStores (.return (.const 0)) := by
  rw [sourceFunctionBody_eq_structural]; rfl

theorem shaStateInit_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer watched : BitVec 64)
    (localPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_state_init)).2.memory watched =
      state.memory watched := by
  rw [source_shaStateInit_stores]
  apply wordStorePlan_memory _ _ _ rfl state pointer watched localPointer
  intro entry member
  have offset : entry.1 < 64 := by
    simp only [shaStateInitStores,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro same
  have natural := congrArg BitVec.toNat same
  have offsetNat : (BitVec.ofNat 64 entry.1).toNat = entry.1 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat] at natural
  rcases outside with before | after <;> omega

theorem shaStateInit_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word pointer)]) (code : state.code = originalRuntimeCode)
    (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_state_init") [argument]) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp",.one)],sourceFunctionBody Guest.guestFn_sha256_state_init,.one) := by
    rw [code]; exact vmLookup_sha256_state_init
  have lookup := pan_single_word_lookup state.code.lookup (ofString "sha256_state_init") (ofString "stp")
    (sourceFunctionBody Guest.guestFn_sha256_state_init) pointer installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "sha256_state_init")
    .one [argument] _ _ _ args lookup run
  have frame := shaStateInit_body_memory
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "stp",.val (.word pointer)))) pointer watched
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) fits outside
  rw [bodyRun] at frame
  rw [postEq]
  exact frame

#print axioms source_shaStateInit_stores
#print axioms shaStateInit_body_memory
#print axioms shaStateInit_call_normal_memory
end InitECandidate.Runtime
