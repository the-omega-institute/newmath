import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_local_naming_exhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff
                dischargeSocket transport route provenance localName bundle pkg)
          (fun row : BHist => hsame row localName)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert ProbeBundle PkgSig
  intro packet
  have packetWitness :
      MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg := packet
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff
                dischargeSocket transport route provenance localName bundle pkg)
          (fun row : BHist => hsame row localName)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName (And.intro (hsame_refl localName) packetWitness)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left provenancePkg
  }
  exact And.intro cert provenancePkg

end BEDC.Derived.MetaCICCriticalPathUp
