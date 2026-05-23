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

theorem CofinalWindowRealSealPublicCertificate [AskSetup] [PackageSetup]
    {B T W D R E X G H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X G publicRead ->
      PkgSig bundle N pkg ->
        PkgSig bundle publicRead pkg ->
          cofinalWindowRealSealFields (CofinalWindowRealSealUp.mk B T W D R E X G H C P N) =
              [B, T, W, D, R, E, X, G, H, C, P, N] ∧
            Cont X G publicRead ∧
              PkgSig bundle N pkg ∧
                PkgSig bundle publicRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row publicRead ∧
                        ∃ packet : CofinalWindowRealSealUp,
                          packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
                    (fun row : BHist => hsame row publicRead)
                    (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro publicRoute namePkg publicPkg
  have sourcePublic :
      (fun row : BHist =>
        hsame row publicRead ∧
          ∃ packet : CofinalWindowRealSealUp,
            packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N) publicRead := by
    exact ⟨hsame_refl publicRead,
      ⟨CofinalWindowRealSealUp.mk B T W D R E X G H C P N, rfl⟩⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row publicRead ∧
            ∃ packet : CofinalWindowRealSealUp,
              packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
        (fun row : BHist => hsame row publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, publicPkg⟩
    }
  exact ⟨rfl, publicRoute, namePkg, publicPkg, cert⟩

end BEDC.Derived.CofinalWindowRealSealUp
