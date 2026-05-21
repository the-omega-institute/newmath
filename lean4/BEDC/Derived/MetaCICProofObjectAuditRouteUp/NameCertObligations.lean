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

theorem MetaCICProofObjectAuditRoutePacket_namecert_obligations [AskSetup] [PackageSetup]
    {S O D N C B H R P L synthesisObstruction dischargeClosed blockedRoute
      localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S O synthesisObstruction ->
      Cont D N dischargeClosed ->
        Cont B R blockedRoute ->
          Cont blockedRoute L localRead ->
            PkgSig bundle localRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row localRead ∧
                    FieldFaithful.fields
                      (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
                      [S, O, D, N, C, B, H, R, P, L])
                (fun row : BHist =>
                  hsame row S ∨ hsame row O ∨ hsame row D ∨ hsame row N ∨
                    hsame row B ∨ Cont B R blockedRoute)
                (fun row : BHist =>
                  hsame row localRead ∧ PkgSig bundle localRead pkg ∧
                    Cont blockedRoute L localRead)
                hsame ∧
                FieldFaithful.fields
                    (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
                  [S, O, D, N, C, B, H, R, P, L] ∧
                Cont S O synthesisObstruction ∧
                  Cont D N dischargeClosed ∧
                    Cont B R blockedRoute ∧
                      Cont blockedRoute L localRead ∧
                        PkgSig bundle localRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro synthesisRoute dischargeRoute blockedRouteCont localRoute localPkg
  have fields_eq :
      FieldFaithful.fields
          (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
        [S, O, D, N, C, B, H, R, P, L] := by
    rfl
  have sourceLocal :
      (fun row : BHist =>
        hsame row localRead ∧
          FieldFaithful.fields
            (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
            [S, O, D, N, C, B, H, R, P, L]) localRead := by
    exact ⟨hsame_refl localRead, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row localRead ∧
            FieldFaithful.fields
              (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L) =
              [S, O, D, N, C, B, H, R, P, L])
        (fun row : BHist =>
          hsame row S ∨ hsame row O ∨ hsame row D ∨ hsame row N ∨ hsame row B ∨
            Cont B R blockedRoute)
        (fun row : BHist =>
          hsame row localRead ∧ PkgSig bundle localRead pkg ∧
            Cont blockedRoute L localRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localRead sourceLocal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr blockedRouteCont))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, localPkg, localRoute⟩
    }
  exact
    ⟨cert, fields_eq, synthesisRoute, dischargeRoute, blockedRouteCont, localRoute,
      localPkg⟩

end BEDC.Derived.MetaCICProofObjectAuditRouteUp
