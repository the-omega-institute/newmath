import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PaperLeanDriftWitnessCarrier [AskSetup] [PackageSetup]
    (M A L I R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont M A L ∧ Cont L I R ∧ Cont R H C ∧
        PkgSig bundle N pkg

theorem PaperLeanDriftWitness_audit_consumer_kernel_scope [AskSetup] [PackageSetup]
    {M A L I R H C P N terminal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R C terminal →
        PkgSig bundle terminal pkg →
          UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
            UnaryHistory R ∧ UnaryHistory terminal ∧ Cont R C terminal ∧
              PkgSig bundle N pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier terminalRoute terminalPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, _hUnary, cUnary, _pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed rUnary cUnary terminalRoute
  exact
    ⟨mUnary, aUnary, lUnary, iUnary, rUnary, terminalUnary, terminalRoute, namePkg,
      terminalPkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
