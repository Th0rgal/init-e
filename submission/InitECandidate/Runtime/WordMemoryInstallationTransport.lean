import InitECandidate.Runtime.WordMemoryInstallation
import InitECandidate.Proofs.InstallationTransport
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Encoders.Asm

theorem panInstalledWordMemory_transport {S Q : Type} {mc : MachineConfig 64 S Q}
    {before after : S} (agreement : InstallationAgreement mc before after)
    {bytes : List (BitVec 8)} {cbspace : Nat} {bitmaps : List (BitVec 64)} {dataSp : Nat}
    {ffiNames : Option (List HolFfiName)} {regs : Nat × Nat}
    {extra : List Compiler.Backend.LabToTarget.ShmemInfoNum}
    {pMem : BitVec 64 → WordLocW 64} {pDom sdm : BitVec 64 → Prop}
    (installed : panInstalledWordMemory bytes cbspace bitmaps dataSp ffiNames regs
      mc extra before pMem pDom sdm) :
    panInstalledWordMemory bytes cbspace bitmaps dataSp ffiNames regs
      mc extra after pMem pDom sdm := by
  rcases installed with ⟨t, m, pointer, bitmapsDm, sharedDm, words, source, initial, rest⟩
  exact ⟨t, m, pointer, bitmapsDm, sharedDm, words, source,
    goodInitState_transport agreement initial,
    by simpa only [agreement.pc] using rest⟩
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.panInstalledWordMemory_transport
