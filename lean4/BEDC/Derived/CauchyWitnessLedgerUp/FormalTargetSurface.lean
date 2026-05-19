import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_formal_target_surface [AskSetup] [PackageSetup]
    {Q B S K H C P N surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B S →
      Cont S K surface →
        hsame H surface →
          hsame C surface →
            hsame P surface →
              hsame N surface →
                PkgSig bundle surface pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row surface ∧
                        ∃ packet : CauchyWitnessLedgerUp,
                          packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                    (fun row : BHist =>
                      Cont Q B S ∧ Cont S K surface ∧ hsame H surface ∧
                        hsame C surface ∧ hsame P surface ∧ hsame N surface ∧
                          hsame row surface)
                    (fun row : BHist => hsame row surface ∧ PkgSig bundle surface pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeS routeSurface sameH sameC sameP sameN surfacePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro surface
          ⟨hsame_refl surface,
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
        ⟨routeS, routeSurface, sameH, sameC, sameP, sameN, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, surfacePkg⟩
  }

theorem CauchyWitnessLedgerUp_StdBridge [AskSetup] [PackageSetup]
    {Q B S K H C P N route terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B route →
      Cont route K terminal →
        PkgSig bundle terminal pkg →
          SemanticNameCert
            (fun row : BHist =>
              ∃ packet : CauchyWitnessLedgerUp,
                packet = CauchyWitnessLedgerUp.mk Q B S K H C P N ∧
                  hsame row terminal)
            (fun row : BHist =>
              hsame row Q ∨ hsame row B ∨ hsame row S ∨ hsame row K ∨
                hsame row terminal)
            (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeQB routeK terminalPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminal
          (Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N)
            ⟨rfl, hsame_refl terminal⟩)
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
        cases source with
        | intro packet packetData =>
            exact
              Exists.intro packet
                ⟨packetData.left,
                  hsame_trans (hsame_symm same) packetData.right⟩
    }
    pattern_sound := by
      intro _row source
      cases source with
      | intro _packet packetData =>
          exact Or.inr (Or.inr (Or.inr (Or.inr packetData.right)))
    ledger_sound := by
      intro _row source
      cases source with
      | intro _packet packetData =>
          exact ⟨packetData.right, terminalPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
