import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TailBudgetCoherenceCarrier [AskSetup] [PackageSetup]
    (meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory meet ∧ UnaryHistory observationBudget ∧ UnaryHistory selectorBudget ∧
    UnaryHistory agreementSeal ∧ UnaryHistory limitSeal ∧ UnaryHistory window ∧
      UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory transport ∧
        UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
          UnaryHistory endpoint ∧ Cont meet observationBudget window ∧
            Cont meet selectorBudget dyadic ∧ Cont window dyadic readback ∧
              Cont readback agreementSeal limitSeal ∧ Cont limitSeal transport routes ∧
                Cont routes provenance localCert ∧ Cont provenance localCert endpoint ∧
                  hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg

theorem TailBudgetCoherenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal
              limitSeal window readback dyadic transport routes provenance localCert endpoint
              bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal
              limitSeal window readback dyadic transport routes provenance localCert endpoint
              bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal
              limitSeal window readback dyadic transport routes provenance localCert endpoint
              bundle pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.TailBudgetCoherenceUp
