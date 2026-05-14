import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_completion_consumer_factorization
    [AskSetup] [PackageSetup]
    {Q B S K H C P N dyadicRoute streamRoute regSeqRoute realRoute
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont dyadicRoute streamRoute regSeqRoute →
      Cont regSeqRoute realRoute completionRead →
        Cont Q B S →
          Cont S K completionRead →
            hsame C completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row completionRead ∧
                      ∃ packet : CauchyWitnessLedgerUp,
                        packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                  (fun row : BHist =>
                    Cont dyadicRoute streamRoute regSeqRoute ∧
                      Cont regSeqRoute realRoute completionRead ∧
                        Cont Q B S ∧ Cont S K completionRead ∧
                          hsame C completionRead ∧ hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro siblingLeft siblingRight routeS routeCompletion sameC completionPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          ⟨hsame_refl completionRead,
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
      exact ⟨siblingLeft, siblingRight, routeS, routeCompletion, sameC, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
