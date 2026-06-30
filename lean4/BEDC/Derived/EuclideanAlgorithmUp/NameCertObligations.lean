import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EuclideanAlgorithmUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EuclideanAlgorithmCarrier [AskSetup] [PackageSetup]
    (I S B T Z H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory I ∧ UnaryHistory S ∧
    UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory P ∧
      Cont I S B ∧ Cont B T Z ∧ Cont Z H C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame N (append C P)

theorem EuclideanAlgorithmCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I S B T Z H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EuclideanAlgorithmCarrier I S B T Z H C P N bundle pkg →
      UnaryHistory I ∧ UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory T ∧
        UnaryHistory Z ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
          UnaryHistory N ∧ Cont I S B ∧ Cont B T Z ∧ Cont Z H C ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame N (append C P) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier
  obtain ⟨inputUnary, stepUnary, terminalUnary, transportUnary, provenanceUnary,
    inputStepRoute, terminalRoute, replayRoute, provenancePkg, namePkg, nameLocal⟩ := carrier
  have budgetUnary : UnaryHistory B :=
    unary_cont_closed inputUnary stepUnary inputStepRoute
  have bezoutUnary : UnaryHistory Z :=
    unary_cont_closed budgetUnary terminalUnary terminalRoute
  have replayUnary : UnaryHistory C :=
    unary_cont_closed bezoutUnary transportUnary replayRoute
  have nameUnary : UnaryHistory N :=
    unary_transport
      (unary_cont_closed replayUnary provenanceUnary rfl)
      (hsame_symm nameLocal)
  exact
    ⟨inputUnary, stepUnary, budgetUnary, terminalUnary, bezoutUnary,
      transportUnary, replayUnary, provenanceUnary, nameUnary, inputStepRoute,
      terminalRoute, replayRoute, provenancePkg, namePkg, nameLocal⟩

end BEDC.Derived.EuclideanAlgorithmUp
