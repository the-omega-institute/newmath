import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_banach_source_readback [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont banach contraction sourceRead ->
        PkgSig bundle sourceRead pkg ->
          UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory iterates ∧
            UnaryHistory sourceRead ∧ Cont banach contraction lipschitz ∧
              Cont banach contraction sourceRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet banachContractionSourceRead sourceReadPkg
  obtain ⟨banachUnary, contractionUnary, _lipschitzUnary, iteratesUnary, _modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed banachUnary contractionUnary banachContractionSourceRead
  exact
    ⟨banachUnary, contractionUnary, iteratesUnary, sourceReadUnary, banachContractionLipschitz,
      banachContractionSourceRead, namePkg, sourceReadPkg⟩

theorem PicardContractionPacket_banach_source_row_scope [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      step sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont endpoint transport sealRead ->
          PkgSig bundle step pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory transport ∧ UnaryHistory step ∧
                  UnaryHistory sealRead ∧ Cont banach contraction lipschitz ∧
                    Cont iterates contraction step ∧ Cont endpoint transport sealRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle step pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesContractionStep endpointTransportSealRead stepPkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, _modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, transportUnary, stepUnary,
      sealReadUnary, banachContractionLipschitz, iteratesContractionStep,
      endpointTransportSealRead, namePkg, stepPkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
