import InitECandidate.Runtime.StackToLabLoop
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Install

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
theorem flattenInstall_bounded (s1 : StackSemStateFiniteExact width C F)
    (ptr len dptr dlen ret : Nat) : BoundedFlattenProp (.install ptr len dptr dlen ret : HolProg width) s1 2 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_install] at ev
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm .install 0 [] 0, .label n l 0] t1.code := by
    simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst
  obtain ⟨fetch0, i2⟩ := lineAt rfl hinst
  obtain ⟨fetch1, i3⟩ := lineAt rfl i2
  obtain ⟨locL, -⟩ := labelAt i3
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, d13, d14, -, -, -, -, -, -, -, h22, h23, h24, -⟩ :=
    id rel
  have hus := (relNoStack rel).1
  rcases hx : StackSemStateOps.getVar t1.ptrReg s1 with _ | ⟨w1 | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar t1.lenReg s1 with _ | ⟨w2 | ⟨_, _⟩⟩ <;>
    rcases hz : StackSemStateOps.getVar dptr s1 with _ | ⟨w3 | ⟨_, _⟩⟩ <;>
    rcases hw : StackSemStateOps.getVar dlen s1 with _ | ⟨w4 | ⟨_, _⟩⟩ <;>
    simp only [hx, hy, hz, hw] at ev <;> try exact (err ev).elim
  rcases ho : s1.compileOracle 0 with ⟨cfg, progs, bm⟩
  have hprogs : (s1.compileOracle 0).2.1 = progs := by rw [ho]
  simp only [ho, hus, Bool.false_eq_true, if_false] at ev
  rcases hfl : wordSemBufferFlush s1.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩
  · simp only [hfl] at ev; exact (err ev).elim
  simp only [hfl] at ev
  rcases hc : s1.compile cfg progs with _ | ⟨bytes', cfg'⟩
  · simp only [hc] at ev; exact (err ev).elim
  simp only [hc] at ev
  rcases hpr : progs with _ | ⟨⟨k, p0⟩, rest⟩
  · rw [hpr] at ev; exact (err ev).elim
  rw [hpr] at ev
  simp only at ev
  split at ev
  swap; · exact (err ev).elim
  rename_i hv
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  rw [← hpr]
  have ho' : t1.compileOracle 0 = (cfg, progs.map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL) := by
    rw [h24]; simp [ho]
  have hc' : t1.compile cfg (progs.map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL) = some (bytes, cfg') := by
    have := congrFun (congrFun h23 cfg) progs
    rw [← this, hc, hv.1]
  have hcfg : (t1.compileOracle 1).1 = cfg' := by
    rw [h24]; simpa [holShiftSeq] using hv.2.2
  have hmap : progs.map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL = ⟨k, (Flapjack.Compiler.Backend.StackToLab.progToSectionHOL (k, p0)).lines⟩ ::
      rest.map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL := by
    rw [hpr]; simp [progToSection_eq]
  refine ⟨2, by decide, { t1 with
      pc := t1.pc + 1 + 1
      codeBuffer := cb
      code := t1.code ++ progs.map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL
      ccRegs := holShiftSeq 1 t1.ccRegs
      ccFpRegs := holShiftSeq 1 t1.ccFpRegs
      regs := fun r => if r = t1.ptrReg then .loc k 0 else
        getRegValue (t1.ccRegs 0 r) (if r = t1.linkReg then .loc n l else t1.regs r)
          WordLocW.word
      fpRegs := fun r => t1.ccFpRegs 0 r
      compileOracle := holShiftSeq 1 t1.compileOracle }, fun ck1 => ?_, rfl, rfl, rfl, rfl,
    rfl, List.prefix_append _ _, ?_, ?_⟩
  · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1 + 1) + 1 by omega, locValueStep _ fetch0 locL]
    refine (installStep (t := { t1 with
        regs := fun key => if key = t1.linkReg then .loc n l else t1.regs key
        pc := t1.pc + 1 }) (w1 := w1) (w2 := w2) (t1.clock + ck1) fetch1
      (by simp [Ne.symm d14, InstCorrect.regOfLookup rel hx])
      (by simp [Ne.symm d13, InstCorrect.regOfLookup rel hy])
      (by simp) (by simpa [← h22] using hfl) locL ho' hc' hmap hcfg).trans ?_
    rfl
  · simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
  · rw [hpr] at hprogs
    have := stateRelInstall rel hprogs bm cb s1.dataBuffer k n l (t1.pc + 1 + 1)
    rw [← hpr] at this
    rwa [hus] at this

end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.flattenInstall_bounded
