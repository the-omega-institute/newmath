import BEDC.Derived.SubjectReductionDischargeLedgerUp.TasteGate
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubjectReductionDischargeLedgerRouteExhaustion
    (x : SubjectReductionDischargeLedgerUp) :
    ∃ beta appArg lambdaDomain piDomain route transport replay provenance name : BHist,
      x = SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route
          transport replay provenance name ∧
        Cont BHist.Empty beta beta ∧ Cont BHist.Empty appArg appArg ∧
          Cont BHist.Empty lambdaDomain lambdaDomain ∧
            Cont BHist.Empty piDomain piDomain ∧
              hsame route (append BHist.Empty route) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | mk beta appArg lambdaDomain piDomain route transport replay provenance name =>
      exact
        ⟨beta, appArg, lambdaDomain, piDomain, route, transport, replay, provenance, name,
          rfl, cont_left_unit beta, cont_left_unit appArg, cont_left_unit lambdaDomain,
          cont_left_unit piDomain, (append_empty_left route).symm⟩

theorem SubjectReductionDischargeLedgerNameCertObligations
    (x : SubjectReductionDischargeLedgerUp) :
    ∃ beta appArg lambdaDomain piDomain route transport replay provenance name : BHist,
      x = SubjectReductionDischargeLedgerUp.mk beta appArg lambdaDomain piDomain route
          transport replay provenance name ∧
        Cont BHist.Empty beta beta ∧ Cont BHist.Empty appArg appArg ∧
          Cont BHist.Empty lambdaDomain lambdaDomain ∧
            Cont BHist.Empty piDomain piDomain ∧
              SemanticNameCert
                (fun row : BHist => hsame row name)
                (fun row : BHist =>
                  hsame row beta ∨ hsame row appArg ∨ hsame row lambdaDomain ∨
                    hsame row piDomain ∨ hsame row route ∨ hsame row name)
                (fun row : BHist => hsame row name)
                hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  cases x with
  | mk beta appArg lambdaDomain piDomain route transport replay provenance name =>
      refine
        ⟨beta, appArg, lambdaDomain, piDomain, route, transport, replay, provenance, name,
          rfl, cont_left_unit beta, cont_left_unit appArg, cont_left_unit lambdaDomain,
          cont_left_unit piDomain, ?_⟩
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro name (hsame_refl name)
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
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.SubjectReductionDischargeLedgerUp
