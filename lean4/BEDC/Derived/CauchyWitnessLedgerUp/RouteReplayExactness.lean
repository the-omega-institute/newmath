import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_route_replay_exactness [AskSetup] [PackageSetup]
    {Q B S K H C P N streamWindow observationRead classifierRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B streamWindow ->
      Cont streamWindow S observationRead ->
        Cont observationRead K classifierRead ->
          Cont classifierRead N realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row realRead ∧
                    ∃ packet : CauchyWitnessLedgerUp,
                      packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                (fun row : BHist =>
                  Cont Q B streamWindow ∧ Cont streamWindow S observationRead ∧
                    Cont observationRead K classifierRead ∧ Cont classifierRead N realRead ∧
                      hsame row realRead)
                (fun row : BHist => hsame row realRead ∧ PkgSig bundle realRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeWindow routeObservation routeClassifier routeReal realPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead
          ⟨hsame_refl realRead,
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
      exact ⟨routeWindow, routeObservation, routeClassifier, routeReal, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
