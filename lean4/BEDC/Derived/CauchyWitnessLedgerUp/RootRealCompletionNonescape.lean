import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_root_real_completion_nonescape
    [AskSetup] [PackageSetup]
    {Q B S K H C P N dyadicRoute streamRoute regSeqRoute realRoute endpoint consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont dyadicRoute streamRoute regSeqRoute →
      Cont regSeqRoute realRoute endpoint →
        Cont Q B S →
          Cont S K endpoint →
            Cont endpoint N consumer →
              hsame N endpoint →
                PkgSig bundle consumer pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row consumer ∧
                        ∃ packet : CauchyWitnessLedgerUp,
                          packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                    (fun row : BHist =>
                      Cont dyadicRoute streamRoute regSeqRoute ∧
                        Cont regSeqRoute realRoute endpoint ∧ Cont Q B S ∧
                          Cont S K endpoint ∧ Cont endpoint N consumer ∧
                            hsame row consumer ∧ hsame N endpoint)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro dyadicStreamReg regRealEndpoint budgetRoute internalRoute consumerRoute
    sameEndpoint consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer,
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
        ⟨dyadicStreamReg, regRealEndpoint, budgetRoute, internalRoute,
          consumerRoute, source.left, sameEndpoint⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
