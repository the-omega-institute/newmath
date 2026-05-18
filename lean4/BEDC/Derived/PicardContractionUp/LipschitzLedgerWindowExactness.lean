import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_lipschitz_ledger_window_exactness [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      ratioRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont lipschitz iterates ratioRead →
        Cont ratioRead routes windowRead →
          PkgSig bundle windowRead pkg →
            UnaryHistory lipschitz ∧ UnaryHistory iterates ∧ UnaryHistory ratioRead ∧
              UnaryHistory windowRead ∧ Cont banach contraction lipschitz ∧
                Cont lipschitz iterates ratioRead ∧ Cont ratioRead routes windowRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet ratioRoute windowRoute windowPkg
  rcases packet with
    ⟨_banachUnary, _contractionUnary, lipschitzUnary, iteratesUnary, _modulusUnary,
      _endpointUnary, _transportUnary, routesUnary, _provenanceUnary, _nameUnary,
      banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
      _routesProvenanceName, namePkg⟩
  have ratioUnary : UnaryHistory ratioRead :=
    unary_cont_closed lipschitzUnary iteratesUnary ratioRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed ratioUnary routesUnary windowRoute
  exact
    ⟨lipschitzUnary, iteratesUnary, ratioUnary, windowUnary, banachContractionLipschitz,
      ratioRoute, windowRoute, namePkg, windowPkg⟩

end BEDC.Derived.PicardContractionUp
