import BEDC.Derived.CofinalModulusNormalizationSealUp.TasteGate

namespace BEDC.Derived.CofinalModulusNormalizationSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CofinalModulusNormalizationSeal_paired_schedule_exposure [AskSetup] [PackageSetup]
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] ->
      Cont A B M ->
        Cont M W sharedRead ->
          Cont sharedRead D dyadicRead ->
            Cont dyadicRead R regularRead ->
              Cont regularRead E sealRead ->
                Cont sealRead L terminalRead ->
                  PkgSig bundle terminalRead pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row M ∧ Cont A B M)
                      (fun row : BHist => hsame row A ∨ hsame row B ∨ hsame row M)
                      (fun _row : BHist =>
                        Cont A B M ∧ Cont M W sharedRead ∧
                          Cont sharedRead D dyadicRead ∧ Cont dyadicRead R regularRead ∧
                            Cont regularRead E sealRead ∧ Cont sealRead L terminalRead ∧
                              PkgSig bundle terminalRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _fieldsExact routeAB routeShared routeDyadic routeRegular routeSeal routeTerminal pkgSig
  exact {
    core := {
      carrier_inhabited := Exists.intro M ⟨hsame_refl M, routeAB⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row _source
      exact
        ⟨routeAB, routeShared, routeDyadic, routeRegular, routeSeal, routeTerminal, pkgSig⟩
  }

end BEDC.Derived.CofinalModulusNormalizationSealUp
