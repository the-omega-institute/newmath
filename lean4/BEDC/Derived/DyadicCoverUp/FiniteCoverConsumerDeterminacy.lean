import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_finite_cover_consumer_determinacy [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint
      coverRead coverRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes coverRead ->
        Cont window routes coverRead' ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row endpoint ∧
                  DyadicCoverPacket centers radii intervals mesh window transport routes
                    provenance nameCert endpoint bundle pkg)
              (fun row : BHist => hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory coverRead ∧ UnaryHistory coverRead' ∧
              hsame coverRead coverRead' ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro packet coverRoute coverRoute'
  have certSurface := DyadicCoverPacket_namecert_obligations packet
  obtain ⟨_centersUnary, _radiiUnary, _intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    _centersRadiiIntervals, _intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed windowUnary routesUnary coverRoute
  have coverUnary' : UnaryHistory coverRead' :=
    unary_cont_closed windowUnary routesUnary coverRoute'
  have sameCover : hsame coverRead coverRead' :=
    cont_deterministic coverRoute coverRoute'
  exact ⟨certSurface.left, coverUnary, coverUnary', sameCover, endpointPkg⟩

end BEDC.Derived.DyadicCoverUp
