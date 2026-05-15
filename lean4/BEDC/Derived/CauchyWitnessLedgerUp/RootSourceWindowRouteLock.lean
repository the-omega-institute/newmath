import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_root_source_window_route_lock [AskSetup] [PackageSetup]
    {Q B S K H C P N streamWindow rationalRead classifierRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B streamWindow ->
      Cont streamWindow S rationalRead ->
        Cont rationalRead K classifierRead ->
          Cont classifierRead N terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row terminalRead ∧
                    ∃ packet : CauchyWitnessLedgerUp,
                      packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                (fun row : BHist =>
                  Cont Q B streamWindow ∧ Cont streamWindow S rationalRead ∧
                    Cont rationalRead K classifierRead ∧ Cont classifierRead N terminalRead ∧
                      hsame row terminalRead)
                (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro windowRoute rationalRoute classifierRoute terminalRoute terminalPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead
          ⟨hsame_refl terminalRead,
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
      exact ⟨windowRoute, rationalRoute, classifierRoute, terminalRoute, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
