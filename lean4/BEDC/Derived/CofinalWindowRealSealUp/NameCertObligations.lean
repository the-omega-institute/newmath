import BEDC.Derived.CofinalWindowRealSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CofinalWindowRealSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CofinalWindowRealSealNameCertObligations [AskSetup] [PackageSetup]
    {B T W D R E X G H C P N windowRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B T windowRead ->
      Cont W D dyadicRead ->
        Cont dyadicRead E sealRead ->
          PkgSig bundle N pkg ->
            PkgSig bundle sealRead pkg ->
              cofinalWindowRealSealFields (CofinalWindowRealSealUp.mk B T W D R E X G H C P N) =
                  [B, T, W, D, R, E, X, G, H, C, P, N] ∧
                Cont B T windowRead ∧
                  Cont W D dyadicRead ∧
                    Cont dyadicRead E sealRead ∧
                      PkgSig bundle N pkg ∧
                        PkgSig bundle sealRead pkg ∧
                          SemanticNameCert
                            (fun row : BHist =>
                              hsame row sealRead ∧
                                ∃ packet : CofinalWindowRealSealUp,
                                  packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
                            (fun row : BHist => hsame row sealRead)
                            (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro budgetWindow windowDyadic dyadicSeal namePkg sealPkg
  have sourceSeal :
      (fun row : BHist =>
        hsame row sealRead ∧
          ∃ packet : CofinalWindowRealSealUp,
            packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N) sealRead := by
    exact ⟨hsame_refl sealRead,
      ⟨CofinalWindowRealSealUp.mk B T W D R E X G H C P N, rfl⟩⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row sealRead ∧
            ∃ packet : CofinalWindowRealSealUp,
              packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
        (fun row : BHist => hsame row sealRead)
        (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, sealPkg⟩
    }
  exact
    ⟨rfl, budgetWindow, windowDyadic, dyadicSeal, namePkg, sealPkg, cert⟩

end BEDC.Derived.CofinalWindowRealSealUp
