import BEDC.Derived.MetacicNormalizationConfluenceBridgeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.MetacicNormalizationConfluenceBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetacicNormalizationConfluenceBridgeRouteBoundary [AskSetup] [PackageSetup]
    {N Q D A T H C P L routeBoundary : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont N Q D ->
      Cont D A T ->
        Cont T H routeBoundary ->
          PkgSig bundle L pkg ->
            metacicNormalizationConfluenceBridgeFields
                (MetacicNormalizationConfluenceBridgeUp.mk N Q D A T H C P L) =
              [N, Q, D, A, T, H, C, P, L] ∧
              SemanticNameCert
                (fun row : BHist => hsame row routeBoundary ∧ Cont T H routeBoundary)
                (fun row : BHist => hsame row routeBoundary ∧ Cont N Q D ∧ Cont D A T)
                (fun row : BHist => hsame row routeBoundary ∧ PkgSig bundle L pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro normalizationRoute dischargeRoute boundaryRoute packageRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeBoundary ∧ Cont T H routeBoundary)
        (fun row : BHist => hsame row routeBoundary ∧ Cont N Q D ∧ Cont D A T)
        (fun row : BHist => hsame row routeBoundary ∧ PkgSig bundle L pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeBoundary ⟨hsame_refl routeBoundary, boundaryRoute⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, normalizationRoute, dischargeRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageRoute⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.MetacicNormalizationConfluenceBridgeUp
