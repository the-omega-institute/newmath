import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TanneryTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TanneryTheoremCarrier [AskSetup] [PackageSetup]
    (array limit majorant windows readback dyadic endpoint transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory array ∧ UnaryHistory limit ∧ UnaryHistory majorant ∧ UnaryHistory windows ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory endpoint ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont array limit majorant ∧ Cont majorant windows readback ∧
          Cont readback dyadic endpoint ∧ Cont endpoint transport route ∧
            Cont route cert provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle cert pkg

theorem TanneryTheoremCarrier_dominated_row_handoff [AskSetup] [PackageSetup]
    {array limit majorant windows readback dyadic endpoint transport route provenance cert
      dominatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint transport route
        provenance cert bundle pkg ->
      Cont array limit dominatedRead ->
        PkgSig bundle dominatedRead pkg ->
          UnaryHistory array ∧ UnaryHistory limit ∧ UnaryHistory majorant ∧
            UnaryHistory dominatedRead ∧ Cont array limit dominatedRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle dominatedRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier dominatedCont dominatedPkg
  obtain ⟨arrayUnary, limitUnary, majorantUnary, _windowsUnary, _readbackUnary, _dyadicUnary,
    _endpointUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _arrayLimitMajorant, _majorantWindowsReadback, _readbackDyadicEndpoint,
    _endpointTransportRoute, _routeCertProvenance, provenancePkg, _certPkg⟩ := carrier
  have dominatedUnary : UnaryHistory dominatedRead :=
    unary_cont_closed arrayUnary limitUnary dominatedCont
  exact
    ⟨arrayUnary, limitUnary, majorantUnary, dominatedUnary, dominatedCont, provenancePkg,
      dominatedPkg⟩

theorem TanneryTheoremCarrier_real_series_exchange_boundary [AskSetup] [PackageSetup]
    {array limit majorant windows readback dyadic endpoint transport route provenance cert
      seriesRead exchangeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TanneryTheoremCarrier array limit majorant windows readback dyadic endpoint transport route
        provenance cert bundle pkg ->
      Cont readback endpoint seriesRead ->
        Cont seriesRead provenance exchangeRead ->
          PkgSig bundle exchangeRead pkg ->
            UnaryHistory readback ∧ UnaryHistory endpoint ∧ UnaryHistory seriesRead ∧
              UnaryHistory exchangeRead ∧ Cont readback endpoint seriesRead ∧
                Cont seriesRead provenance exchangeRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle exchangeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier seriesCont exchangeCont exchangePkg
  obtain ⟨_arrayUnary, _limitUnary, _majorantUnary, _windowsUnary, readbackUnary,
    _dyadicUnary, endpointUnary, _transportUnary, _routeUnary, provenanceUnary,
    _certUnary, _arrayLimitMajorant, _majorantWindowsReadback, _readbackDyadicEndpoint,
    _endpointTransportRoute, _routeCertProvenance, provenancePkg, _certPkg⟩ := carrier
  have seriesUnary : UnaryHistory seriesRead :=
    unary_cont_closed readbackUnary endpointUnary seriesCont
  have exchangeUnary : UnaryHistory exchangeRead :=
    unary_cont_closed seriesUnary provenanceUnary exchangeCont
  exact
    ⟨readbackUnary, endpointUnary, seriesUnary, exchangeUnary, seriesCont, exchangeCont,
      provenancePkg, exchangePkg⟩

end BEDC.Derived.TanneryTheoremUp
