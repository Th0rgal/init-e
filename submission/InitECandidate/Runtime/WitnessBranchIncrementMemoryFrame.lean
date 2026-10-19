import InitECandidate.Runtime.WitnessBranchFinishMemoryFrame
import InitECandidate.Runtime.WitnessBranchMoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_branch_increment_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchAt 4) = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat → watched≠top+32 → post.memory watched=s.memory watched := by
  rw [source_witness_branch_increment] at run
  obtain ⟨selected,incrementRun,tailRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  obtain ⟨value,evaluated,selectedEq⟩ := evaluate_local_assign_normal_value s selected _ _ incrementRun
  have valueEq : value=.val (.word (index+1)) := by
    simpa [evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord] using evaluated.symm
  subst value
  have other (name : MlS) (different : name≠ofString "i") : selected.locals.lookup name=s.locals.lookup name := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have selectedIndex : selected.locals.lookup (ofString "i")=some (.val (.word (index+1))) := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have selectedGlobals : selected.globals=s.globals := by rw [selectedEq];rfl
  have selectedMemory : selected.memory=s.memory := by rw [selectedEq];rfl
  have selectedDomain : selected.memaddrs=s.memaddrs := by rw [selectedEq];rfl
  by_cases more : Compiler.Encoders.Asm.wordCmpHOL .less (index+1) (16#64)=true
  · have condition : @evalHOLExact 64 F _ selected.toExact (fun a => Classical.propDecidable (selected.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.const 16))=some (.val (.word (1#64))) := by
      simp only [evalHOLExact,selectedIndex]
      change (some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .less (index+1) (16#64)=true then 1 else 0))) : Option (ValueHOL 64))=_
      rw [more]
      rfl
    rw [source_witness_branch_dispatch,evaluateHOLFiniteState_ite,condition] at tailRun
    change evaluateHOLFiniteState selected witnessBranchMore=(none,post) at tailRun
    have globals := witness_branch_more_globals_frame selected (by rw [selectedEq];exact code)
    rw [tailRun] at globals
    have allGlobals := globals.trans selectedGlobals
    refine ⟨?_,?_,?_,?_⟩
    · rw [allGlobals];exact scratchGlobal
    · rw [allGlobals];exact frameGlobal
    · rw [allGlobals]
    · intro watched above below separate
      have memory := witness_branch_more_word_frame selected top (index+1) watched
        ((other _ (by decide)).trans atTop) selectedIndex separate
      rw [tailRun] at memory
      exact memory.trans (congrFun selectedMemory watched)
  · have condition : @evalHOLExact 64 F _ selected.toExact (fun a => Classical.propDecidable (selected.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.const 16))=some (.val (.word (0#64))) := by
      simp only [evalHOLExact,selectedIndex]
      change (some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .less (index+1) (16#64)=true then 1 else 0))) : Option (ValueHOL 64))=_
      rw [if_neg more]
      rfl
    rw [source_witness_branch_dispatch,evaluateHOLFiniteState_ite,condition] at tailRun
    change evaluateHOLFiniteState selected (witnessBranchFinishAt 0)=(none,post) at tailRun
    obtain ⟨scratchPost,framePost,heapPost,memory⟩ := witness_branch_finish_normal_memory_frame selected post
      array pointer length scratch frame top heap ceiling inputLimit
      (by rw [selectedDomain];exact arrayReadable) (by rw [selectedMemory];exact arrayCell)
      ((other _ (by decide)).trans atTop) ((other _ (by decide)).trans atBr) heapBound
      (slice.after_frame s selected array 16 pointer length selectedDomain (congrFun selectedMemory _) (congrFun selectedMemory _))
      inputRange lengthBound limitBound (by rw [selectedGlobals];exact scratchGlobal) (by rw [selectedGlobals];exact frameGlobal)
      (by rw [selectedEq];exact code) orderedFrame framePositive scratchBelow
      (by intro address lower upper;rw [selectedDomain];exact arena address lower upper)
      (by rw [selectedEq];exact budget) tailRun
    exact ⟨scratchPost,framePost,heapPost.trans (by rw [selectedGlobals]),
      fun watched above below _ => (memory watched above below).trans (congrFun selectedMemory watched)⟩

#print axioms witness_branch_increment_normal_memory_frame
end InitECandidate.Runtime
