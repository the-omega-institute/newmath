import BEDC.Derived.RealityConstrainedModelAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedModelAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedModelAuditFailureSurfaceExhaustion [AskSetup] [PackageSetup]
    {H Pi O M C T L F S failureRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realityConstrainedModelAuditFields (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
        [H, Pi, O, M, C, T, L, F, S] ->
      Cont C F failureRead ->
        Cont L F ledgerRead ->
          PkgSig bundle failureRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row failureRead ∧
                    realityConstrainedModelAuditFields
                        (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
                      [H, Pi, O, M, C, T, L, F, S])
                (fun row : BHist => hsame row F ∨ Cont C F row ∨ Cont L F row)
                (fun row : BHist => hsame row failureRead ∧ PkgSig bundle failureRead pkg)
                hsame ∧
              hsame F F ∧ Cont C F failureRead ∧ Cont L F ledgerRead ∧
                PkgSig bundle failureRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro fieldsExact failureRoute ledgerRoute packageFailure
  have sourceFailure :
      (fun row : BHist =>
        hsame row failureRead ∧
          realityConstrainedModelAuditFields
              (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
            [H, Pi, O, M, C, T, L, F, S]) failureRead := by
    exact ⟨hsame_refl failureRead, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row failureRead ∧
              realityConstrainedModelAuditFields
                  (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
                [H, Pi, O, M, C, T, L, F, S])
          (fun row : BHist => hsame row F ∨ Cont C F row ∨ Cont L F row)
          (fun row : BHist => hsame row failureRead ∧ PkgSig bundle failureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro failureRead sourceFailure
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
      exact Or.inr (Or.inl (cont_result_hsame_transport failureRoute (hsame_symm source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageFailure⟩
  }
  exact ⟨cert, hsame_refl F, failureRoute, ledgerRoute, packageFailure⟩

end BEDC.Derived.RealityConstrainedModelAuditUp
