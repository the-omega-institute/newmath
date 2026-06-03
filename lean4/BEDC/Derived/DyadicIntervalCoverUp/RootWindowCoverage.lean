import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicIntervalCoverRootObligationSurface [AskSetup] [PackageSetup]
    (L U M R V W Q A H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory L ∧
    UnaryHistory U ∧
      UnaryHistory M ∧
        UnaryHistory R ∧
          UnaryHistory V ∧
            UnaryHistory W ∧
              UnaryHistory Q ∧
                UnaryHistory A ∧
                  UnaryHistory H ∧
                    UnaryHistory C ∧
                      UnaryHistory P ∧
                        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem DyadicIntervalCoverRootWindowCoverage [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory windowRead ∧
                UnaryHistory coverRead ∧ UnaryHistory sealRead ∧ Cont W Q windowRead ∧
                  Cont M R coverRead ∧ Cont coverRead A sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface windowCont coverCont sealCont sealPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  exact
    ⟨wUnary, qUnary, windowUnary, coverUnary, sealUnary, windowCont, coverCont, sealCont,
      pPkg, sealPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
