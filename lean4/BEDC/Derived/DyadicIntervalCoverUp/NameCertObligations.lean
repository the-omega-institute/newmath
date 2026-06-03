import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverNamecertObligations [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont endpointRead V sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
                  UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory sealRead ∧ Cont L U endpointRead ∧
                      Cont W Q windowRead ∧ Cont endpointRead V sealRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface endpointCont windowCont sealCont sealPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have nPkg : PkgSig bundle N pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary vUnary sealCont
  exact
    ⟨lUnary, uUnary, mUnary, rUnary, vUnary, wUnary, qUnary, aUnary, endpointUnary,
      windowUnary, sealUnary, endpointCont, windowCont, sealCont, pPkg, nPkg, sealPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
