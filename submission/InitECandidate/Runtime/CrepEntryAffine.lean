import InitECandidate.Runtime.CrepEntryCeiling
import InitECandidate.Runtime.BaselineCrepState
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRelEvaluateCallCorrect
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Basis.Pure.MlString

private theorem crepSimpProgHOL_call_none_nil {width : Nat} [NeZero width]
    (start : MlString) :
    crepSimpProgHOL (.call none start [] : CrepProgHOL width) = .call none start [] := by
  conv => lhs; unfold crepSimpProgHOL
  rfl

private theorem compileHOLExact_call_none_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (start : MlString) :
    compileHOLExact (width := width) ctxt .ln (.call none start []) =
      .seq (.call none (some (findLabExact ctxt start)) [] none) .skip := by
  simp [compileHOLExact, compileExpsHOLExact, genTemps, loopNestedSeqHOL]

/-- Numerical version of the original whole-program entry bridge, retaining
its arithmetic simplification and all original entry premises. -/
theorem crep_entry_affine {width : Nat} [NeZero width] {σ : Type}
    (nctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width))
    (start : MlString) (s : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width)) (lc : Nat)
    (prog : CrepProgHOL width) (limit : Nat)
    (small : sizeOf (CrepProgHOL.call none start [] : CrepProgHOL width) ≤ limit)
    (bounded : CrepCodeSize limit (crepSimpMapcsHOL s)) :
    crepToLoopCodeRel2Exact nctxt s_code t_code →
    evalCrepSemHOLProgExact s (.call none start []) = (res, s') →
    s.be = t.be ∧ s.shMemaddrs = (fun address => t.shMdomain address = true) ∧
      s.memaddrs = (fun address => t.mdomain address = true) ∧ s.clock = t.clock ∧
      s.ffi = t.ffi ∧ s.baseAddr = t.baseAddr ∧ s.topAddr = t.topAddr ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      s.locals = HolFiniteMapExact.empty ∧
      s.code = s_code ∧ t.code = t_code →
    (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
      some (findLabExact nctxt start, 0) →
    findLabExact nctxt start = lc ∧
      s.code = alistToFmapCodeExact crep_code ∧
      nctxt.funcs = crepToLoopMakeFuncsExactHOL crep_code ∧
      holAlookup crep_code start = some ([], prog) ∧
      crepToLoopDistinctVarsExact nctxt.vars ∧
      crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars →
    res ≠ some .error →
    ∃ (k : Nat), k ≤ ((5 * limit + 5) * s.clock + 2 * limit) ∧ ∃ (res' : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t' : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate
          (.call none (some (findLabExact nctxt start)) [] none)
          { t with clock := t.clock + k } = (res', t') ∧
      crepToLoopStateRelExact s' t' ∧
      res' = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res := by
  intro hcode2 he ⟨hbe, hsh, hmd, hclk, hffi, hbase, htop, hmem, hglob, hloc, hsc, htc⟩
    _hmf ⟨_hlc, _halist, _hfuncs, _halookup, hdistinct, hmax⟩ hne
  have hsimp := crepArithSimpProgCorrect (.call none start []) s res s' he hne
  rw [crepSimpProgHOL_call_none_nil] at hsimp
  have hcodeRel : crepToLoopCodeRelExact nctxt (crepSimpMapcsHOL s).code t.code := by
    have h : crepToLoopCodeRelExact nctxt
        (s_code.map2 (fun entry =>
          match entry with
          | (_, parameters, program) => (parameters, crepSimpProgHOL program))) t_code :=
      hcode2
    rw [← hsc, ← htc] at h
    exact h
  have hlocals : crepToLoopLocalsRelExact nctxt .ln (crepSimpMapcsHOL s).locals t.locals := by
    refine ⟨hdistinct, hmax, ?_, ?_⟩
    · intro n hn
      simp [sptMem, sptDomain, sptLookup] at hn
    · intro vname value hlookup
      change s.locals.lookup vname = some value at hlookup
      rw [hloc] at hlookup
      simp [HolFiniteMapExact.empty] at hlookup
  have hstate : crepToLoopStateRelExact (crepSimpMapcsHOL s) t :=
    ⟨hmd, hsh, hclk, hbe, hffi, hbase, htop⟩
  obtain ⟨ck, ckSmall, res1, t1, hrun, hstate', _, _, _, hres, _⟩ :=
    crep_affine_fuel limit (.call none start []) (crepSimpMapcsHOL s) small bounded res
      (crepSimpMapcsHOL s') t nctxt .ln
      hsimp hne hstate hmem hglob hcodeRel hlocals
  rw [compileHOLExact_call_none_nil, LoopSemStateFiniteExact.evaluate_Seq_Skip] at hrun
  exact ⟨ck, ckSmall, res1, t1, hrun, hstate', hres⟩

#print axioms crep_entry_affine
end InitECandidate.Runtime
