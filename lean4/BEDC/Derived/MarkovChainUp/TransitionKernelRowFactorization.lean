import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MarkovChainTransitionCarrier_transition_kernel_row_factorization [AskSetup]
    [PackageSetup] {prob random law transition controw provenance endpoint kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      Cont random transition kernelRead ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory prob ∧ UnaryHistory random ∧ UnaryHistory law ∧
            UnaryHistory transition ∧ UnaryHistory kernelRead ∧ UnaryHistory provenance ∧
              UnaryHistory endpoint ∧ Cont random transition kernelRead ∧
                Cont prob law provenance ∧ Cont provenance kernelRead endpoint ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier kernelRoute endpointPkg
  have probUnary : UnaryHistory prob := carrier.left
  have randomUnary : UnaryHistory random := carrier.right.left
  have lawUnary : UnaryHistory law := carrier.right.right.left
  have transitionUnary : UnaryHistory transition := carrier.right.right.right.left
  have controwUnary : UnaryHistory controw := carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint := carrier.right.right.right.right.right.right.left
  have controwRoute : Cont random transition controw :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceRoute : Cont prob law provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have endpointRoute : Cont provenance controw endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have sameKernel : hsame controw kernelRead :=
    cont_respects_hsame (hsame_refl random) (hsame_refl transition) controwRoute kernelRoute
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed randomUnary transitionUnary kernelRoute
  have endpointKernelRoute : Cont provenance kernelRead endpoint :=
    cont_hsame_transport (hsame_refl provenance) sameKernel (hsame_refl endpoint) endpointRoute
  exact
    ⟨probUnary,
      randomUnary,
      lawUnary,
      transitionUnary,
      kernelUnary,
      provenanceUnary,
      endpointUnary,
      kernelRoute,
      provenanceRoute,
      endpointKernelRoute,
      endpointPkg⟩

end BEDC.Derived.MarkovChainUp
