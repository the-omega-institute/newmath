import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootCompactHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead windowRead sealRead compactRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont M R coverRead →
          Cont W Q windowRead →
            Cont coverRead A sealRead →
              Cont endpointRead sealRead compactRead →
                PkgSig bundle compactRead pkg →
                  UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory compactRead ∧ Cont L U endpointRead ∧
                        Cont M R coverRead ∧ Cont W Q windowRead ∧
                          Cont coverRead A sealRead ∧
                            Cont endpointRead sealRead compactRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface endpointCont coverCont windowCont sealCont compactCont compactPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed endpointUnary sealUnary compactCont
  exact
    ⟨endpointUnary, coverUnary, windowUnary, sealUnary, compactUnary, endpointCont,
      coverCont, windowCont, sealCont, compactCont, pPkg, compactPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
