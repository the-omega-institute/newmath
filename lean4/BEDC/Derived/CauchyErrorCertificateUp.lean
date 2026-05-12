import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyErrorCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyErrorCertificatePacket [AskSetup] [PackageSetup]
    (readback modulus tail budget provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧ UnaryHistory budget ∧
    UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont modulus tail budget ∧
      Cont readback budget provenance ∧ PkgSig bundle readback pkg ∧
        PkgSig bundle provenance pkg

theorem CauchyErrorCertificatePacket_namecert_obligations [AskSetup] [PackageSetup]
    {readback modulus tail budget provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        (fun row : BHist => hsame row readback)
        (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
        hsame ∧ UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧
          UnaryHistory budget ∧ PkgSig bundle readback pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary, _provenanceUnary,
    _nameCertUnary, _modulusTailBudget, _readbackBudgetProvenance, readbackPkg,
    _provenancePkg⟩ := packet
  have sourceWitness :
      (fun row : BHist =>
        hsame row readback ∧
          CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
            bundle pkg) readback := by
    exact And.intro (hsame_refl readback) packetWitness
  have core :
      NameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro readback sourceWitness
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHReadback : hsame h readback := sourceH.left
        have sameKReadback : hsame k readback :=
          hsame_trans (hsame_symm sameHK) sameHReadback
        exact And.intro sameKReadback sourceH.right
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        (fun row : BHist => hsame row readback)
        (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro h source
        exact source.left
      ledger_sound := by
        intro h source
        exact And.intro source.left readbackPkg
    }
  exact
    And.intro cert
      (And.intro readbackUnary
        (And.intro modulusUnary (And.intro tailUnary (And.intro budgetUnary readbackPkg))))

end BEDC.Derived.CauchyErrorCertificateUp
