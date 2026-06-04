import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularModulusCarrier [AskSetup] [PackageSetup]
    (S mu D W H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory ProbeBundle Pkg PkgSig
  UnaryHistory S ∧ UnaryHistory mu ∧ UnaryHistory D ∧ UnaryHistory W ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularModulusRegSeqRatHandoff [AskSetup] [PackageSetup]
    {S mu D W H C P N modulusRead dyadicRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularModulusCarrier S mu D W H C P N bundle pkg →
      Cont S mu modulusRead →
        Cont modulusRead D dyadicRead →
          Cont dyadicRead W handoffRead →
            PkgSig bundle handoffRead pkg →
              UnaryHistory modulusRead ∧ UnaryHistory dyadicRead ∧
                UnaryHistory handoffRead ∧ Cont S mu modulusRead ∧
                  Cont modulusRead D dyadicRead ∧ Cont dyadicRead W handoffRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceModulus modulusDyadic dyadicWindow handoffPkg
  have sUnary : UnaryHistory S := carrier.left
  have muUnary : UnaryHistory mu := carrier.right.left
  have dUnary : UnaryHistory D := carrier.right.right.left
  have wUnary : UnaryHistory W := carrier.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.left
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sUnary muUnary sourceModulus
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed modulusUnary dUnary modulusDyadic
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed dyadicUnary wUnary dyadicWindow
  exact
    ⟨modulusUnary, dyadicUnary, handoffUnary, sourceModulus, modulusDyadic,
      dyadicWindow, pPkg, handoffPkg⟩

end BEDC.Derived.RegularModulusUp
