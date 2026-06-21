import BEDC.Derived.EpistemicWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EpistemicWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EpistemicWitnessCarrier [AskSetup] [PackageSetup]
    (claim witness auditRoute strength gap bridge transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory claim ∧ UnaryHistory witness ∧ UnaryHistory auditRoute ∧
    UnaryHistory strength ∧ UnaryHistory gap ∧ UnaryHistory bridge ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont witness auditRoute replay ∧
          Cont strength gap bridge ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem EpistemicWitnessCarrier_audit_surface [AskSetup] [PackageSetup]
    {claim witness auditRoute strength gap bridge transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpistemicWitnessCarrier claim witness auditRoute strength gap bridge transport replay
      provenance localName bundle pkg →
      UnaryHistory claim ∧ UnaryHistory witness ∧ UnaryHistory auditRoute ∧
        Cont witness auditRoute replay ∧ Cont strength gap bridge ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig
  intro carrier
  obtain ⟨claimUnary, witnessUnary, auditUnary, _strengthUnary, _gapUnary, _bridgeUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, auditReplay,
    strengthBoundary, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨claimUnary, witnessUnary, auditUnary, auditReplay, strengthBoundary, provenancePkg,
      localNamePkg⟩

end BEDC.Derived.EpistemicWitnessUp
