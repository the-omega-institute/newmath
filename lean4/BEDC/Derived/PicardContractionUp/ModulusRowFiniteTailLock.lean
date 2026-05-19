import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_modulus_row_finite_tail_lock [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates modulus modulusRead →
        PkgSig bundle modulusRead pkg →
          UnaryHistory iterates ∧ UnaryHistory lipschitz ∧ UnaryHistory modulus ∧
            UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory modulusRead ∧
              Cont iterates modulus modulusRead ∧ Cont endpoint transport routes ∧
                PkgSig bundle name pkg ∧ PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusRead modulusReadPkg
  obtain ⟨_banachUnary, _contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    _endpointUnary, transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  exact
    ⟨iteratesUnary, lipschitzUnary, modulusUnary, transportUnary, routesUnary,
      modulusReadUnary, iteratesModulusRead, endpointTransportRoutes, namePkg,
      modulusReadPkg⟩

end BEDC.Derived.PicardContractionUp
