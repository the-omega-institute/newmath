import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootWindowObligations [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory windowRead ∧
                  UnaryHistory coverRead ∧ UnaryHistory sealRead ∧ UnaryHistory namedRead ∧
                    Cont W Q windowRead ∧ Cont M R coverRead ∧
                      Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface windowCont coverCont sealCont namedCont namedPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedCont
  exact
    ⟨wUnary, qUnary, windowUnary, coverUnary, sealUnary, namedUnary, windowCont, coverCont,
      sealCont, namedCont, pPkg, namedPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
