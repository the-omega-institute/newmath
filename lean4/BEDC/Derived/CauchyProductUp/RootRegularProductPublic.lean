import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_regular_product_public_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name seriesTail seriesSeal publicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes seriesTail ->
        Cont seriesTail ledger seriesSeal ->
          Cont seriesSeal routes publicSeal ->
            PkgSig bundle publicSeal pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory seriesTail ∧
                UnaryHistory seriesSeal ∧ UnaryHistory publicSeal ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes seriesTail ∧ Cont seriesTail ledger seriesSeal ∧
                      Cont seriesSeal routes publicSeal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle publicSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet seriesTailRoute seriesSealRoute publicSealRoute publicSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have seriesTailUnary : UnaryHistory seriesTail :=
    unary_cont_closed classifierUnary routesUnary seriesTailRoute
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesTailUnary ledgerUnary seriesSealRoute
  have publicSealUnary : UnaryHistory publicSeal :=
    unary_cont_closed seriesSealUnary routesUnary publicSealRoute
  exact
    ⟨productUnary, classifierUnary, seriesTailUnary, seriesSealUnary, publicSealUnary,
      productRoute, classifierRoute, seriesTailRoute, seriesSealRoute, publicSealRoute,
      namePkg, publicSealPkg⟩

end BEDC.Derived.CauchyProductUp
