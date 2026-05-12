import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegseqratStreamCertificateSpine [AskSetup] [PackageSetup]
    (streamCarrier regularityLedger observationIndex ratEndpoint tolerance provenance
      sealRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory streamCarrier ∧ UnaryHistory regularityLedger ∧ UnaryHistory observationIndex ∧
    UnaryHistory ratEndpoint ∧ Cont streamCarrier observationIndex ratEndpoint ∧
      Cont ratEndpoint tolerance regularityLedger ∧ Cont regularityLedger provenance sealRow ∧
        PkgSig bundle sealRow pkg

theorem RegseqratStreamCertificateSpine_carrier_projection [AskSetup] [PackageSetup]
    {streamCarrier regularityLedger observationIndex ratEndpoint tolerance provenance sealRow
      observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegseqratStreamCertificateSpine streamCarrier regularityLedger observationIndex ratEndpoint
        tolerance provenance sealRow bundle pkg ->
      Cont observationIndex ratEndpoint observationRead ->
        UnaryHistory streamCarrier ∧ UnaryHistory observationIndex ∧
          UnaryHistory ratEndpoint ∧ UnaryHistory observationRead ∧
            Cont streamCarrier observationIndex ratEndpoint ∧ PkgSig bundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro spine observationRoute
  obtain ⟨streamUnary, _regularityUnary, observationUnary, endpointUnary, streamRoute,
    _regularityRoute, _sealRoute, sealPkg⟩ := spine
  have observationReadUnary : UnaryHistory observationRead :=
    unary_cont_closed observationUnary endpointUnary observationRoute
  exact
    ⟨streamUnary, observationUnary, endpointUnary, observationReadUnary, streamRoute,
      sealPkg⟩

end BEDC.Derived.RealUp
