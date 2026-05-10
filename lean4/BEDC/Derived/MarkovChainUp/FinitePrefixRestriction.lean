import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MarkovChainBHistTransitionCarrier_finite_prefix_restriction_carrier
    [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint prefixCont prefixEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      Cont random transition prefixCont ->
        Cont provenance prefixCont prefixEndpoint ->
          PkgSig bundle prefixEndpoint pkg ->
            MarkovChainBHistTransitionCarrier prob random law transition prefixCont provenance
                prefixEndpoint bundle pkg ∧
              hsame controw prefixCont ∧ hsame endpoint prefixEndpoint := by
  intro carrier prefixContRow prefixEndpointRow prefixPkg
  have sameControw : hsame controw prefixCont :=
    cont_respects_hsame (hsame_refl random) (hsame_refl transition)
      carrier.right.right.right.right.right.right.right.left prefixContRow
  have sameEndpoint : hsame endpoint prefixEndpoint :=
    cont_respects_hsame (hsame_refl provenance) sameControw
      carrier.right.right.right.right.right.right.right.right.right.left prefixEndpointRow
  have prefixContUnary : UnaryHistory prefixCont :=
    unary_cont_closed carrier.right.left carrier.right.right.right.left prefixContRow
  have prefixEndpointUnary : UnaryHistory prefixEndpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left prefixContUnary prefixEndpointRow
  have restrictedCarrier :
      MarkovChainBHistTransitionCarrier prob random law transition prefixCont provenance
        prefixEndpoint bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      prefixContUnary,
      carrier.right.right.right.right.right.left,
      prefixEndpointUnary,
      prefixContRow,
      carrier.right.right.right.right.right.right.right.right.left,
      prefixEndpointRow,
      prefixPkg⟩
  exact ⟨restrictedCarrier, sameControw, sameEndpoint⟩

end BEDC.Derived.MarkovChainUp
