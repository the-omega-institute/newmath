import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapDependencyWeaveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AuditMapDependencyWeaveCarrier [AskSetup] [PackageSetup]
    (localMap neighbour obstruction frontier synthesis transport continuation provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory localMap ∧ UnaryHistory neighbour ∧ UnaryHistory obstruction ∧
    UnaryHistory frontier ∧ UnaryHistory synthesis ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont localMap neighbour transport ∧ Cont obstruction frontier continuation ∧
          Cont synthesis transport provenance ∧ PkgSig bundle provenance pkg

theorem AuditMapDependencyWeaveRouteAdmission [AskSetup] [PackageSetup]
    {localMap neighbour obstruction frontier synthesis transport continuation provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapDependencyWeaveCarrier localMap neighbour obstruction frontier synthesis transport
        continuation provenance localName bundle pkg →
      Cont continuation localName route →
        PkgSig bundle route pkg →
          UnaryHistory localMap ∧ UnaryHistory neighbour ∧ UnaryHistory obstruction ∧
            UnaryHistory frontier ∧ UnaryHistory synthesis ∧ UnaryHistory route ∧
              Cont continuation localName route ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont routePkg
  rcases carrier with
    ⟨localMapUnary, neighbourUnary, obstructionUnary, frontierUnary, synthesisUnary,
      _transportUnary, continuationUnary, _provenanceUnary, localNameUnary,
      _mapTransport, _obstructionContinuation, _synthesisProvenance, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed continuationUnary localNameUnary routeCont
  exact
    ⟨localMapUnary, neighbourUnary, obstructionUnary, frontierUnary, synthesisUnary,
      routeUnary, routeCont, provenancePkg, routePkg⟩

end BEDC.Derived.AuditMapDependencyWeaveUp
