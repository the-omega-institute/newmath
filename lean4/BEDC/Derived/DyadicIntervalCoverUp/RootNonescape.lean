import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootNonescape [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead coverRead sealRead compactRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont M R coverRead →
            Cont coverRead A sealRead →
              Cont endpointRead sealRead compactRead →
                Cont compactRead N namedRead →
                  PkgSig bundle namedRead pkg →
                    UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory compactRead ∧ UnaryHistory namedRead ∧
                          Cont L U endpointRead ∧ Cont W Q windowRead ∧
                            Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                              Cont endpointRead sealRead compactRead ∧
                                Cont compactRead N namedRead ∧
                                  PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface endpointRoute windowRoute coverRoute sealRoute compactRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed endpointUnary sealUnary compactRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed compactUnary nUnary namedRoute
  exact
    ⟨endpointUnary, windowUnary, coverUnary, sealUnary, compactUnary, namedUnary,
      endpointRoute, windowRoute, coverRoute, sealRoute, compactRoute, namedRoute,
      namedPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
