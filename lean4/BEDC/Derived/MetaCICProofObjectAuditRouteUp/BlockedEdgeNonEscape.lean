import BEDC.Derived.MetaCICProofObjectAuditRouteUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.MetaCICProofObjectAuditRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem MetaCICProofObjectAuditRoute_blocked_edge_nonescape [AskSetup] [PackageSetup]
    {S O D N C B H R P L closedNormalRead obstructionRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont N B closedNormalRead ->
      Cont O D obstructionRead ->
        Cont closedNormalRead obstructionRead auditRead ->
          PkgSig bundle auditRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row auditRead ∧
                  FieldFaithful.fields
                    (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
                    [S, O, D, N, C, B, H, R, P, L])
              (fun row : BHist =>
                hsame row N ∨ hsame row B ∨ hsame row O ∨ hsame row D ∨
                  Cont N B closedNormalRead ∨ Cont O D obstructionRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
              FieldFaithful.fields
                  (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
                [S, O, D, N, C, B, H, R, P, L] ∧
              hsame B B ∧
                Cont N B closedNormalRead ∧
                  Cont O D obstructionRead ∧
                    Cont closedNormalRead obstructionRead auditRead ∧
                      PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro closedNormalRoute obstructionRoute auditRoute auditPkg
  have fields_eq :
      FieldFaithful.fields
          (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
        [S, O, D, N, C, B, H, R, P, L] := by
    rfl
  have sourceAudit :
      (fun row : BHist =>
        hsame row auditRead ∧
          FieldFaithful.fields
            (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
            [S, O, D, N, C, B, H, R, P, L]) auditRead := by
    exact ⟨hsame_refl auditRead, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row auditRead ∧
            FieldFaithful.fields
              (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
              [S, O, D, N, C, B, H, R, P, L])
        (fun row : BHist =>
          hsame row N ∨ hsame row B ∨ hsame row O ∨ hsame row D ∨
            Cont N B closedNormalRead ∨ Cont O D obstructionRead)
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro auditRead sourceAudit
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
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl closedNormalRoute))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, auditPkg⟩
    }
  exact
    ⟨cert, fields_eq, hsame_refl B, closedNormalRoute, obstructionRoute, auditRoute,
      auditPkg⟩

end BEDC.Derived.MetaCICProofObjectAuditRouteUp
