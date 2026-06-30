import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationRefinementStabilityBudget [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localStep glueStep : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont J L localStep →
        Cont localStep G glueStep →
          UnaryHistory J ∧ UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory localStep ∧
            UnaryHistory glueStep ∧ UnaryHistory H ∧ UnaryHistory R ∧
              PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier refinementRoute gluingRoute
  obtain ⟨_cUnary, _tUnary, jUnary, _pUnary, lUnary, gUnary, _sUnary, hUnary, rUnary,
    _qUnary, _nUnary, provenancePkg, namePkg⟩ := carrier
  have localStepUnary : UnaryHistory localStep :=
    unary_cont_closed jUnary lUnary refinementRoute
  have glueStepUnary : UnaryHistory glueStep :=
    unary_cont_closed localStepUnary gUnary gluingRoute
  exact
    ⟨jUnary, lUnary, gUnary, localStepUnary, glueStepUnary, hUnary, rUnary,
      provenancePkg, namePkg⟩

end BEDC.Derived.SheafificationUp
