import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_cauchy_modulus_handoff [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      modulusRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus modulusRead ->
        Cont modulusRead endpoint cauchyRead ->
          PkgSig bundle modulusRead pkg ->
            PkgSig bundle cauchyRead pkg ->
              UnaryHistory modulus ∧ UnaryHistory modulusRead ∧ UnaryHistory cauchyRead ∧
                Cont iterates modulus endpoint ∧ Cont iterates modulus modulusRead ∧
                  Cont modulusRead endpoint cauchyRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle modulusRead pkg ∧ PkgSig bundle cauchyRead pkg := by
  intro packet iteratesModulusRead modulusReadEndpointCauchyRead modulusReadPkg cauchyReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed modulusReadUnary endpointUnary modulusReadEndpointCauchyRead
  exact
    ⟨modulusUnary, modulusReadUnary, cauchyReadUnary, iteratesModulusEndpoint,
      iteratesModulusRead, modulusReadEndpointCauchyRead, namePkg, modulusReadPkg,
      cauchyReadPkg⟩

end BEDC.Derived.PicardContractionUp
