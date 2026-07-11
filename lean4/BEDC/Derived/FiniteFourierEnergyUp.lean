import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FiniteFourierEnergyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteFourierEnergy_parseval_route [AskSetup] [PackageSetup]
    {timeSamples frequencySamples parsevalBudget energyRead transport replay provenance
      localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory timeSamples →
      UnaryHistory frequencySamples →
        UnaryHistory parsevalBudget →
          UnaryHistory energyRead →
            UnaryHistory replay →
              UnaryHistory localName →
                Cont timeSamples frequencySamples parsevalBudget →
                  Cont parsevalBudget energyRead transport →
                    Cont transport replay endpoint →
                      PkgSig bundle provenance pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row timeSamples ∨ hsame row frequencySamples ∨
                                hsame row parsevalBudget ∨ hsame row energyRead ∨
                                  hsame row transport ∨ hsame row replay ∨
                                    hsame row provenance ∨ hsame row localName ∨
                                      hsame row endpoint)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                Cont timeSamples frequencySamples parsevalBudget ∧
                                  Cont parsevalBudget energyRead transport ∧
                                    Cont transport replay endpoint ∧
                                      PkgSig bundle provenance pkg)
                            hsame ∧
                          UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro timeUnary frequencyUnary parsevalUnary energyUnary replayUnary _localNameUnary
    parsevalRoute energyRoute endpointRoute provenancePkg
  have parsevalRouteUnary : UnaryHistory parsevalBudget :=
    unary_cont_closed timeUnary frequencyUnary parsevalRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed parsevalRouteUnary energyUnary energyRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary replayUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row timeSamples ∨ hsame row frequencySamples ∨
              hsame row parsevalBudget ∨ hsame row energyRead ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont timeSamples frequencySamples parsevalBudget ∧
              Cont parsevalBudget energyRead transport ∧ Cont transport replay endpoint ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, parsevalRoute, energyRoute, endpointRoute, provenancePkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.FiniteFourierEnergyUp
