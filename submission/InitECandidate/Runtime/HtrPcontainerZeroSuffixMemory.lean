import InitECandidate.Runtime.HtrPcontainerBitmapSuffixMemory
import InitECandidate.Runtime.MemzeroNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPcontainer_zero_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap temporary active out mark count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atTemporary : state.locals.lookup (ofString "tmp") = some (.val (.word temporary)))
    (atActive : state.locals.lookup (ofString "act") = some (.val (.word active)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (aligned : active.toNat % 8 = 0)
    (fits : active.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < active.toNat ∨ active.toNat + 32 ≤ watched.toNat)
    (budget : count.toNat + 135 ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPcontainer_zero] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have frame := memzero_call_normal_memory state middle _ active 32 watched
    (by simp [evalListHOLExact,evalHOLExact,atActive]) layout.code aligned fits outside normal
  have globals := memzero_call_globals_frame [.var .local (ofString "act"),.const 32] state layout.code
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "act"),.const 32])
  have bounded := (memzero_const_progBounded (.var .local (ofString "act")) 32 (by decide)) state layout.code
    (by change 16 ≤ state.clock; omega)
  rw [normal] at globals metadata bounded
  have spent : state.clock ≤ middle.clock + 16 := bounded.1
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by rw [frame.2]
  have suffix := htrPcontainer_bitmap_suffix_returned_memory middle post sha accelerator zeroHashes heap temporary active out mark count watched value
    (layout.transfer globals metadata.1) ((keep _).trans atTemporary) ((keep _).trans atActive)
    ((keep _).trans atOut) ((keep _).trans atMark) ((keep _).trans atCount) small aligned fits outside (by omega) tail
  exact suffix.trans frame.1

/-- The actual active-bitmap pointer declaration and complete remaining suffix
preserve a word before the freshly allocated 64-byte temporary. -/
theorem htrPcontainer_active_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap temporary out mark count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atTemporary : state.locals.lookup (ofString "tmp") = some (.val (.word temporary)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (aligned : temporary.toNat % 8 = 0)
    (fits : temporary.toNat + 64 ≤ 33806089496) (before : watched.toNat < temporary.toNat)
    (budget : count.toNat + 135 ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPcontainer_act] at run
  obtain ⟨active,output,initialized,bodyRun,postEq⟩ := evaluate_dec_returned_scope state post (ofString "act") .one _ _ value run
  have eval : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "tmp"),.const 32]) = some (.val (.word (temporary + (32#64)))) := by
    simp [evalHOLExact,evalListHOLExact,atTemporary,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [eval] at initialized
  obtain rfl := (Option.some.inj initialized).symm
  let ready := setVarHOLFinite (ofString "act") (.val (.word (temporary + (32#64)))) state
  have natural : (temporary + (32#64)).toNat = temporary.toNat + 32 := word_add_toNat temporary 32 (by omega)
  have keep (key : MlS) (different : key ≠ ofString "act") : ready.locals.lookup key = state.locals.lookup key := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have suffix := htrPcontainer_zero_suffix_returned_memory ready output sha accelerator zeroHashes heap temporary
    (temporary + (32#64)) out mark count watched value (layout.transfer rfl rfl)
    ((keep _ (by decide)).trans atTemporary)
    (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark) ((keep _ (by decide)).trans atCount) small
    (by rw [natural,Nat.add_mod,aligned]) (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) budget bodyRun
  rw [postEq]
  exact suffix

#print axioms htrPcontainer_zero_suffix_returned_memory
#print axioms htrPcontainer_active_suffix_returned_memory
end InitECandidate.Runtime
