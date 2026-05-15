import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_observer_filter_budget_selector_lock
    [AskSetup] [PackageSetup]
    {Q B S K H C P N observerWindow observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B observerWindow →
      Cont observerWindow S K →
        Cont K N observerRead →
          hsame H observerWindow →
            hsame C observerRead →
              hsame P observerRead →
                PkgSig bundle observerRead pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row observerRead ∧
                        ∃ packet : CauchyWitnessLedgerUp,
                          packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                    (fun row : BHist =>
                      Cont Q B observerWindow ∧ Cont observerWindow S K ∧
                        Cont K N observerRead ∧ hsame row observerRead)
                    (fun row : BHist => hsame row observerRead ∧
                      PkgSig bundle observerRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeWindow routeK routeRead _sameH _sameC _sameP observerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro observerRead
          ⟨hsame_refl observerRead,
            Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeWindow, routeK, routeRead, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, observerPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
