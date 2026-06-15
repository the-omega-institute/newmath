import BEDC.Derived.WritingItemAuditUp.TasteGate

namespace BEDC.Derived.WritingItemAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem WritingItemAudit_obligation_closure_route [AskSetup] [PackageSetup]
    {K C R L T F G Q H U P N admitted named claimRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont K C admitted ->
      Cont admitted R L ->
        Cont T F G ->
          Cont Q H U ->
            Cont U P named ->
              Cont named Q claimRead ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row named ∧ Cont U P named ∧
                      PkgSig bundle named pkg)
                    (fun row : BHist => hsame row named ∧ Cont K C admitted ∧
                      Cont admitted R L ∧ Cont T F G ∧ Cont Q H U ∧ Cont U P named)
                    (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
                    hsame ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row claimRead ∧ Cont named Q claimRead)
                      (fun row : BHist =>
                        hsame row named ∨ hsame row claimRead ∨ hsame row G)
                      (fun _row : BHist => PkgSig bundle named pkg ∧
                        Cont named Q claimRead)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro admittedRoute ledgerRoute transportRoute queryRoute namedRoute claimRoute pkgNamed
  have base :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ Cont U P named ∧ PkgSig bundle named pkg)
          (fun row : BHist => hsame row named ∧ Cont K C admitted ∧ Cont admitted R L ∧
            Cont T F G ∧ Cont Q H U ∧ Cont U P named)
          (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
          hsame :=
    (WritingItemAudit_namecert_obligations (_N := N) admittedRoute ledgerRoute transportRoute
      queryRoute namedRoute pkgNamed).left
  have claimCert :
      SemanticNameCert
          (fun row : BHist => hsame row claimRead ∧ Cont named Q claimRead)
          (fun row : BHist => hsame row named ∨ hsame row claimRead ∨ hsame row G)
          (fun _row : BHist => PkgSig bundle named pkg ∧ Cont named Q claimRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro claimRead ⟨hsame_refl claimRead, claimRoute⟩
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
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inl sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨pkgNamed, sourceRow.right⟩
    }
  exact ⟨base, claimCert⟩

theorem WritingItemAudit_sibling_dependency [AskSetup] [PackageSetup]
    {K C R L T F _G Q _H U P _N discipline packet admitted named packetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont discipline packet admitted ->
      Cont K C discipline ->
        Cont R L packet ->
          Cont U P named ->
            Cont named packet packetRead ->
              PkgSig bundle named pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row packetRead ∧ Cont named packet packetRead)
                    (fun row : BHist =>
                      hsame row packetRead ∨ hsame row discipline ∨ hsame row packet ∨
                        hsame row K ∨ hsame row Q ∨ hsame row T ∨ hsame row F)
                    (fun _row : BHist =>
                      PkgSig bundle named pkg ∧ Cont discipline packet admitted ∧
                        Cont named packet packetRead)
                    hsame ∧
                  Cont K C discipline ∧ Cont R L packet := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro disciplinePacketAdmitted kindDiscipline classifierPacket namedRoute packetReadRoute
    pkgNamed
  have packetCert :
      SemanticNameCert
          (fun row : BHist => hsame row packetRead ∧ Cont named packet packetRead)
          (fun row : BHist =>
            hsame row packetRead ∨ hsame row discipline ∨ hsame row packet ∨ hsame row K ∨
              hsame row Q ∨ hsame row T ∨ hsame row F)
          (fun _row : BHist =>
            PkgSig bundle named pkg ∧ Cont discipline packet admitted ∧
              Cont named packet packetRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro packetRead ⟨hsame_refl packetRead, packetReadRoute⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inl sourceRow.left
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨pkgNamed, disciplinePacketAdmitted, packetReadRoute⟩
    }
  exact ⟨packetCert, kindDiscipline, classifierPacket⟩

end BEDC.Derived.WritingItemAuditUp
