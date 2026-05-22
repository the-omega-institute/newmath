import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteTriangleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionRouteTriangleCarrier [AskSetup] [PackageSetup]
    (B S F E O L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory E ∧
    UnaryHistory O ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont B C E ∧ Cont O C L ∧
        hsame E H ∧ PkgSig bundle P pkg

theorem SubjectReductionRouteTriangle_bundle_projection [AskSetup] [PackageSetup]
    {B S F E O L H C P N bundleEndpoint : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    SubjectReductionRouteTriangleCarrier B S F E O L H C P N bundle pkg →
      Cont B C bundleEndpoint →
        PkgSig bundle bundleEndpoint pkg →
          UnaryHistory B ∧ UnaryHistory bundleEndpoint ∧ Cont B C bundleEndpoint ∧
            PkgSig bundle bundleEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier bundleRoute bundlePkg
  obtain ⟨bundleUnary, _setupUnary, _conversionUnary, _endpointUnary, _obstructionUnary,
    _ledgerUnary, _transportUnary, componentUnary, _provenanceUnary, _nameUnary,
    _bundleEndpointRoute, _obstructionLedgerRoute, _endpointTransport, _carrierPkg⟩ :=
    carrier
  have bundleEndpointUnary : UnaryHistory bundleEndpoint :=
    unary_cont_closed bundleUnary componentUnary bundleRoute
  exact ⟨bundleUnary, bundleEndpointUnary, bundleRoute, bundlePkg⟩

end BEDC.Derived.SubjectReductionRouteTriangleUp
