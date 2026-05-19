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

theorem RealityConstrainedModelAuditFitSeparation [AskSetup] [PackageSetup]
    {H Pi O M C T L F S observedRead separationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H Pi observedRead →
      Cont O M C →
        Cont C F separationRead →
          PkgSig bundle separationRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row separationRead ∧
                    ∃ packet : RealityConstrainedModelAuditUp,
                      packet = RealityConstrainedModelAuditUp.mk H Pi O M C T L F S ∧
                        realityConstrainedModelAuditFields packet =
                          [H, Pi, O, M, C, T, L, F, S])
                (fun row : BHist => Cont H Pi observedRead ∧ Cont O M C ∧ Cont C F row)
                (fun row : BHist =>
                  hsame row separationRead ∧ PkgSig bundle separationRead pkg ∧ hsame F F)
                hsame ∧
              realityConstrainedModelAuditFields
                  (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
                [H, Pi, O, M, C, T, L, F, S] ∧
                Cont O M C ∧ Cont C F separationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro observedRoute comparisonRoute separationRoute packageSeparation
  have fieldsExact :
      realityConstrainedModelAuditFields
          (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
        [H, Pi, O, M, C, T, L, F, S] := by
    rfl
  have sourceSeparation :
      (fun row : BHist =>
        hsame row separationRead ∧
          ∃ packet : RealityConstrainedModelAuditUp,
            packet = RealityConstrainedModelAuditUp.mk H Pi O M C T L F S ∧
              realityConstrainedModelAuditFields packet =
                [H, Pi, O, M, C, T, L, F, S]) separationRead := by
    exact
      ⟨hsame_refl separationRead, RealityConstrainedModelAuditUp.mk H Pi O M C T L F S,
        rfl, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row separationRead ∧
              ∃ packet : RealityConstrainedModelAuditUp,
                packet = RealityConstrainedModelAuditUp.mk H Pi O M C T L F S ∧
                  realityConstrainedModelAuditFields packet =
                    [H, Pi, O, M, C, T, L, F, S])
          (fun row : BHist => Cont H Pi observedRead ∧ Cont O M C ∧ Cont C F row)
          (fun row : BHist =>
            hsame row separationRead ∧ PkgSig bundle separationRead pkg ∧ hsame F F)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separationRead sourceSeparation
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨observedRoute, comparisonRoute, separationRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageSeparation, hsame_refl F⟩
  }
  exact ⟨cert, fieldsExact, comparisonRoute, separationRoute⟩

end BEDC.Derived.RealityConstrainedModelAuditUp
