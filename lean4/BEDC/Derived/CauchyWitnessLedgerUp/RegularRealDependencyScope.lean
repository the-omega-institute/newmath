import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_regular_real_dependency_scope [AskSetup] [PackageSetup]
    {Q B S K H C P N dyadicRoute streamRoute regSeqRoute realRoute synchronizer classifier
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B S →
      Cont S K endpoint →
        Cont dyadicRoute streamRoute regSeqRoute →
          Cont regSeqRoute realRoute endpoint →
            hsame H synchronizer →
              hsame C classifier →
                PkgSig bundle endpoint pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row endpoint ∧
                        ∃ packet : CauchyWitnessLedgerUp,
                          packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                    (fun row : BHist =>
                      Cont Q B S ∧ Cont S K endpoint ∧
                        Cont dyadicRoute streamRoute regSeqRoute ∧
                          Cont regSeqRoute realRoute endpoint ∧
                            hsame H synchronizer ∧ hsame C classifier ∧
                              hsame row endpoint)
                    (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro ledgerRoute endpointRoute dyadicStreamRoute regSeqRealRoute sameSynchronizer
    sameClassifier endpointPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint
          ⟨hsame_refl endpoint,
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
      exact
        ⟨ledgerRoute, endpointRoute, dyadicStreamRoute, regSeqRealRoute,
          sameSynchronizer, sameClassifier, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
