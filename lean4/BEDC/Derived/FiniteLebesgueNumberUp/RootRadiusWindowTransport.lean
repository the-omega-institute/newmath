import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootRadiusWindowTransport_certificate [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow transportedRadius radiusAudit :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      hsame transportedRadius radius →
        Cont transportedRadius mesh radiusAudit →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row radiusAudit ∧ UnaryHistory row)
                (fun row : BHist => hsame row transportedRadius ∨ hsame row radiusAudit)
                (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row radiusAudit)
                hsame ∧
              UnaryHistory transportedRadius ∧ UnaryHistory radiusAudit ∧
                Cont transportedRadius mesh radiusAudit ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameTransported radiusAuditRoute provenancePkg
  have transported :
      UnaryHistory transportedRadius ∧ UnaryHistory radiusAudit ∧
        SemanticNameCert
          (fun row : BHist => hsame row radiusAudit ∧ UnaryHistory row)
          (fun row : BHist => hsame row transportedRadius ∨ hsame row radiusAudit)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row radiusAudit)
          hsame :=
    FiniteLebesgueNumberRadiusTransport carrier sameTransported radiusAuditRoute provenancePkg
  exact
    ⟨transported.right.right, transported.left, transported.right.left, radiusAuditRoute,
      provenancePkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
