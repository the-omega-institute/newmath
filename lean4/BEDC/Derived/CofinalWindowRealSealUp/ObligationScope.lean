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

theorem CofinalWindowRealSealObligationScope [AskSetup] [PackageSetup]
    {B T W D R E X G H C P N windowRead dyadicRead sealRead boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B T windowRead ->
      Cont W D dyadicRead ->
        Cont dyadicRead E sealRead ->
          Cont X G boundaryRead ->
            Cont E boundaryRead publicRead ->
              PkgSig bundle N pkg ->
                PkgSig bundle publicRead pkg ->
                  cofinalWindowRealSealFields
                      (CofinalWindowRealSealUp.mk B T W D R E X G H C P N) =
                    [B, T, W, D, R, E, X, G, H, C, P, N] /\
                    Cont X G boundaryRead /\
                      Cont E boundaryRead publicRead /\
                        PkgSig bundle publicRead pkg /\
                          SemanticNameCert
                            (fun row : BHist => hsame row publicRead)
                            (fun row : BHist => Cont E boundaryRead row)
                            (fun row : BHist =>
                              hsame row publicRead /\ PkgSig bundle publicRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro _windowRoute _dyadicRoute _sealRoute boundaryRoute publicRoute _namePkg publicPkg
  have sourcePublic : (fun row : BHist => hsame row publicRead) publicRead := by
    exact hsame_refl publicRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead)
        (fun row : BHist => Cont E boundaryRead row)
        (fun row : BHist => hsame row publicRead /\ PkgSig bundle publicRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
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
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact cont_result_hsame_transport publicRoute (hsame_symm source)
      ledger_sound := by
        intro _row source
        exact ⟨source, publicPkg⟩
    }
  exact ⟨rfl, boundaryRoute, publicRoute, publicPkg, cert⟩

end BEDC.Derived.CofinalWindowRealSealUp
