import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegSeqRatUp

theorem RealRegSeqRatFiniteRequest_fusion [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback sealRow request : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
      UnaryHistory sealRow ->
        Cont readback sealRow request ->
          PkgSig bundle request pkg ->
            UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
              UnaryHistory request ∧ Cont regularity provenance readback ∧
                Cont readback sealRow request ∧ PkgSig bundle readback pkg ∧
                  PkgSig bundle request pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealUnary readbackSealRequest requestPkg
  rcases carrier with
    ⟨scheduleUnary, _indexUnary, _endpointUnary, _radiusUnary, _regularityUnary,
      _provenanceUnary, readbackUnary, _scheduleIndexEndpoint,
      _endpointRadiusRegularity, regularityProvenanceReadback, readbackPkg⟩
  have requestUnary : UnaryHistory request :=
    unary_cont_closed readbackUnary sealUnary readbackSealRequest
  exact
    ⟨scheduleUnary, readbackUnary, sealUnary, requestUnary, regularityProvenanceReadback,
      readbackSealRequest, readbackPkg, requestPkg⟩

end BEDC.Derived.RealUp
