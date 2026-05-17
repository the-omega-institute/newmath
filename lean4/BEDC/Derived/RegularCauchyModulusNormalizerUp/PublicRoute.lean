import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_public_route [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      comparisonRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont window dyadic comparisonRead ->
        Cont route provenance publicRead ->
          PkgSig bundle comparisonRead pkg ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
                UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                  UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                    UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                      UnaryHistory comparisonRead ∧ UnaryHistory publicRead ∧
                        Cont muX muY meet ∧ Cont meet window dyadic ∧
                          Cont window dyadic comparisonRead ∧
                            Cont dyadic readback sealRow ∧
                              Cont sealRow transport route ∧
                                Cont route provenance publicRead ∧
                                  PkgSig bundle meet pkg ∧ PkgSig bundle name pkg ∧
                                    PkgSig bundle comparisonRead pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowDyadicComparison routeProvenancePublic comparisonPkg publicPkg
  rcases carrier with
    ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      muXmuYMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
      _routeProvenanceName, meetPkg, namePkg⟩
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicComparison
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  exact
    ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      comparisonUnary, publicUnary, muXmuYMeet, meetWindowDyadic, windowDyadicComparison,
      dyadicReadbackSeal, sealTransportRoute, routeProvenancePublic, meetPkg, namePkg,
      comparisonPkg, publicPkg⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
