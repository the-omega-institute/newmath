import BEDC.Derived.SubstitutionAuditMapUp.Core

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem SubstitutionAuditMapCarrier_closed_boundary_scope [AskSetup] [PackageSetup]
    {T C R S K G H Q P N boundaryRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier T C R S K G H Q P N bundle pkg →
      Cont T C boundaryRead →
        Cont R S K →
          Cont H Q routeRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row boundaryRead ∧
                      SubstitutionAuditMapCarrier T C R S K G H Q P N bundle pkg)
                  (fun row : BHist => Cont T C row ∧ Cont R S K)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont H Q routeRead ∧ PkgSig bundle N pkg)
                  hsame ∧
                Cont T C boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier boundaryRoute substitutionRoute replayRoute packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact ⟨boundaryRead, hsame_refl boundaryRead, carrier⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨cont_result_hsame_transport boundaryRoute (hsame_symm source.left),
            substitutionRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, replayRoute, packageName⟩
    }
  · exact boundaryRoute

end BEDC.Derived.SubstitutionAuditMapUp
