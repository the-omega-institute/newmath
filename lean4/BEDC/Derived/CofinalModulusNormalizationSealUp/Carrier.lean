import BEDC.Derived.CofinalModulusNormalizationSealUp.TasteGate

namespace BEDC.Derived.CofinalModulusNormalizationSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CofinalModulusNormalizationSealCarrier
    (A B M W D R E H C P L N : BHist) : Prop :=
  cofinalModulusNormalizationSealFields
      (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
    [A, B, M, W, D, R, E, H, C, P, L, N]

theorem CofinalModulusNormalizationSealCarrier_shared_window_route [AskSetup]
    [PackageSetup]
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalModulusNormalizationSealCarrier A B M W D R E H C P L N →
      Cont A B M →
        Cont M W sharedRead →
          Cont sharedRead D dyadicRead →
            Cont dyadicRead R regularRead →
              Cont regularRead E sealRead →
                Cont sealRead L terminalRead →
                  PkgSig bundle terminalRead pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row terminalRead ∧
                          CofinalModulusNormalizationSealCarrier A B M W D R E H C P L N)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                          hsame row E ∨ hsame row terminalRead)
                      (fun row : BHist =>
                        hsame row terminalRead ∧ Cont A B M ∧ Cont M W sharedRead ∧
                          Cont sharedRead D dyadicRead ∧ Cont dyadicRead R regularRead ∧
                            Cont regularRead E sealRead ∧ Cont sealRead L terminalRead ∧
                              PkgSig bundle terminalRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeAB routeShared routeDyadic routeRegular routeSeal routeTerminal pkgSig
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, carrier⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, routeAB, routeShared, routeDyadic, routeRegular, routeSeal,
          routeTerminal, pkgSig⟩
  }

end BEDC.Derived.CofinalModulusNormalizationSealUp
