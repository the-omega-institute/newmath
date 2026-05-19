import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_real_envelope_coverage_exactness [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      streamRead regularRead realRead envelopeConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes incidence ->
        Cont incidence routes streamRead ->
          Cont streamRead routes regularRead ->
            Cont regularRead routes realRead ->
              Cont endpoint routes envelopeConsumer ->
                PkgSig bundle realRead pkg ->
                  PkgSig bundle envelopeConsumer pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row endpoint ∧
                            DyadicCoverPacket centers radii intervals mesh window transport routes
                              provenance nameCert endpoint bundle pkg)
                        (fun row : BHist => hsame row endpoint)
                        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                        hsame ∧
                      UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
                        UnaryHistory mesh ∧ UnaryHistory window ∧ UnaryHistory incidence ∧
                          UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                            UnaryHistory realRead ∧ UnaryHistory envelopeConsumer ∧
                              Cont centers radii intervals ∧ Cont intervals mesh window ∧
                                Cont window routes incidence ∧ Cont incidence routes streamRead ∧
                                  Cont streamRead routes regularRead ∧
                                    Cont regularRead routes realRead ∧
                                      Cont endpoint routes envelopeConsumer ∧
                                        PkgSig bundle endpoint pkg ∧
                                          PkgSig bundle realRead pkg ∧
                                            PkgSig bundle envelopeConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet windowRoutesIncidence incidenceRoutesStream streamRoutesRegular
    regularRoutesReal endpointRoutesEnvelope realPkg envelopePkg
  have certSurface := DyadicCoverPacket_namecert_obligations packet
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed incidenceUnary routesUnary incidenceRoutesStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routesUnary streamRoutesRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary routesUnary regularRoutesReal
  have envelopeUnary : UnaryHistory envelopeConsumer :=
    unary_cont_closed endpointUnary routesUnary endpointRoutesEnvelope
  exact
    ⟨certSurface.left, centersUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
      incidenceUnary, streamUnary, regularUnary, realUnary, envelopeUnary,
      centersRadiiIntervals, intervalsMeshWindow, windowRoutesIncidence,
      incidenceRoutesStream, streamRoutesRegular, regularRoutesReal, endpointRoutesEnvelope,
      endpointPkg, realPkg, envelopePkg⟩

end BEDC.Derived.DyadicCoverUp
