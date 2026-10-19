import InitECandidate.Runtime.ProgressiveFoldMemory
import InitECandidate.Runtime.NormalWhileInvariantByGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveFold_tail_globals : OriginalGlobalsFrame progressiveFoldTail := shaPair_call_globals_frame _

theorem progressiveFold_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator roots acc initial watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atK : state.locals.lookup (ofString "k") = some (.val (.word initial)))
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : initial.toNat * 137 ≤ state.clock)
    (run : evaluateHOLFiniteState state progressiveFoldLoop = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.globals.lookup (ofString "sha_st") = some (.val (.word pointer)) ∧
      current.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      current.locals.lookup (ofString "roots") = some (.val (.word roots)) ∧
      current.locals.lookup (ofString "acc") = some (.val (.word acc)) ∧ current.code = originalRuntimeCode ∧
      ∃ k : BitVec 64, current.locals.lookup (ofString "k") = some (.val (.word k)) ∧ k.toNat * 137 ≤ current.clock
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ _ Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,pointerLocal,accelLocal,rootsLocal,accLocal,installed,k,counter,remaining⟩ := invariant
    have positive : 0 < k.toNat := by
      by_contra stopped
      have zero : k = 0 := BitVec.eq_of_toNat_eq (by change k.toNat = 0; omega)
      subst k
      exact nonzero (by simpa [evalHOLFinite_eq_toExact,evalHOLExact,counter,Compiler.Encoders.Asm.wordCmpHOL] using guard.symm)
    let entered := setVarHOLFinite (ofString "k") (.val (.word (k - (1#64)))) (decClockHOLFinite current)
    rw [evaluateHOLFiniteState_seq_line780,evaluate_countdown_assign (decClockHOLFinite current) (ofString "k") k counter] at bodyRun
    change evaluateHOLFiniteState entered progressiveFoldTail = (none,next) at bodyRun
    have keepEntry (key : MlS) (different : key ≠ ofString "k") : entered.locals.lookup key = current.locals.lookup key := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,decClockHOLFinite]
    have enteredCounter : entered.locals.lookup (ofString "k") = some (.val (.word (k - (1#64)))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have enough : 136 ≤ entered.clock := by change 136 ≤ current.clock - 1; omega
    have frame := progressiveFold_tail_normal_memory entered next pointer accelerator roots acc (k - (1#64)) watched
      pointerLocal accelLocal ((keepEntry _ (by decide)).trans rootsLocal) ((keepEntry _ (by decide)).trans accLocal)
      enteredCounter accAligned accFits accBefore accelAligned accelFits pointerFits accelOutside pointerOutside installed (by omega) bodyRun
    have keep (key : MlS) : next.locals.lookup key = entered.locals.lookup key := by
      have locals := evaluate_avoidsLocal_flowing key progressiveFoldTail rfl entered (by rw [bodyRun]; exact Or.inl rfl)
      simpa only [bodyRun] using locals
    have globals := progressiveFold_tail_globals entered installed
    have meta' := evaluateHOLFiniteState_metadata entered progressiveFoldTail
    have spent := (progressiveFold_tail_bounded entered installed enough).1
    rw [bodyRun] at globals meta' spent
    have natural : (k - (1#64)).toNat = k.toNat - 1 :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ k.toNat; omega))
    refine ⟨frame.trans memory,?_,?_,(keep _).trans ((keepEntry _ (by decide)).trans rootsLocal),
      (keep _).trans ((keepEntry _ (by decide)).trans accLocal),meta'.1.trans installed,
      k - (1#64),(keep _).trans enteredCounter,?_⟩
    · rw [globals]; exact pointerLocal
    · rw [globals]; exact accelLocal
    · rw [natural]
      change current.clock - 1 ≤ next.clock + 136 at spent
      omega)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,atAccel,atRoots,atAcc,code,initial,atK,budget⟩ run
  exact finalInvariant.1

#print axioms progressiveFold_tail_globals
#print axioms progressiveFold_loop_normal_memory
end InitECandidate.Runtime
