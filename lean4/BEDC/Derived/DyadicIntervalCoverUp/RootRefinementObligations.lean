import BEDC.Derived.DyadicIntervalCoverUp.RootRefinementCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootRefinementObligations [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N refinedEndpoint refinedCover refinedWindow refinedSeal
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U refinedEndpoint ->
        Cont M R refinedCover ->
          Cont W Q refinedWindow ->
            Cont refinedWindow A refinedSeal ->
              Cont refinedCover refinedSeal namedRead ->
                PkgSig bundle namedRead pkg ->
                  UnaryHistory refinedEndpoint ∧ UnaryHistory refinedCover ∧
                    UnaryHistory refinedWindow ∧ UnaryHistory refinedSeal ∧
                      UnaryHistory namedRead ∧ Cont L U refinedEndpoint ∧
                        Cont M R refinedCover ∧ Cont W Q refinedWindow ∧
                          Cont refinedWindow A refinedSeal ∧
                            Cont refinedCover refinedSeal namedRead ∧
                              PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro surface endpointRoute coverRoute windowRoute sealRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory refinedEndpoint :=
    unary_cont_closed lUnary uUnary endpointRoute
  have coverUnary : UnaryHistory refinedCover :=
    unary_cont_closed mUnary rUnary coverRoute
  have windowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed wUnary qUnary windowRoute
  have sealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed windowUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed coverUnary sealUnary namedRoute
  exact
    ⟨endpointUnary, coverUnary, windowUnary, sealUnary, namedUnary, endpointRoute,
      coverRoute, windowRoute, sealRoute, namedRoute, namedPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
