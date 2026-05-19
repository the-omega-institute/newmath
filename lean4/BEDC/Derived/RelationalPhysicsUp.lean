import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RelationalPhysicsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RelationalPhysicsCarrier [AskSetup] [PackageSetup]
    (observer invariant locality audit rate transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory observer ∧ UnaryHistory invariant ∧ UnaryHistory locality ∧
    UnaryHistory audit ∧ UnaryHistory rate ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont locality invariant audit ∧
        Cont audit rate route ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem RelationalPhysics_namecert_handoff [AskSetup] [PackageSetup]
    {observer invariant locality audit rate transport route provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalPhysicsCarrier observer invariant locality audit rate transport route provenance
        name bundle pkg →
      Cont locality invariant audit →
        Cont audit rate handoff →
          PkgSig bundle handoff pkg →
            UnaryHistory observer ∧ UnaryHistory locality ∧ UnaryHistory invariant ∧
              UnaryHistory audit ∧ UnaryHistory rate ∧ UnaryHistory handoff ∧
                Cont locality invariant audit ∧ Cont audit rate handoff ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier localityInvariantAudit auditRateHandoff handoffPkg
  obtain ⟨observerUnary, invariantUnary, localityUnary, auditUnary, rateUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _carrierLocalityInvariantAudit, _carrierAuditRateRoute, provenancePkg, _namePkg⟩ :=
    carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditUnary rateUnary auditRateHandoff
  exact
    ⟨observerUnary, localityUnary, invariantUnary, auditUnary, rateUnary, handoffUnary,
      localityInvariantAudit, auditRateHandoff, provenancePkg, handoffPkg⟩

end BEDC.Derived.RelationalPhysicsUp
