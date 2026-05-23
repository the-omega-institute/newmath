import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_threshold_budget_exposure [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      UnaryHistory meet ∧ UnaryHistory observationBudget ∧ UnaryHistory selectorBudget ∧
        Cont meet observationBudget window ∧ Cont meet selectorBudget dyadic ∧
          UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  exact ⟨carrier.left, carrier.right.left, carrier.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.left, carrier.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.left⟩

end BEDC.Derived.TailBudgetCoherenceUp
