import BEDC.Derived.WritingItemAuditUp.TasteGate

namespace BEDC.Derived.WritingItemAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem WritingItemAudit_bridge_schema_route [AskSetup] [PackageSetup]
    {K C R L T F G Q H U P _N discipline packet registryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont discipline packet registryRead ->
      Cont K C discipline ->
        Cont R L packet ->
          Cont T F G ->
            Cont registryRead Q H ->
              Cont H U P ->
                PkgSig bundle P pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row registryRead ∧
                      Cont discipline packet registryRead)
                    (fun row : BHist =>
                      hsame row discipline ∨ hsame row packet ∨ hsame row T ∨
                        hsame row F ∨ hsame row G ∨ hsame row Q ∨
                          hsame row registryRead)
                    (fun _row : BHist =>
                      PkgSig bundle P pkg ∧ Cont registryRead Q H ∧ Cont H U P)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro registryRoute _disciplineRoute _packetRoute _statusRoute registryStatusRoute
    statusPublicRoute publicPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro registryRead ⟨hsame_refl registryRead, registryRoute⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨publicPkg, registryStatusRoute, statusPublicRoute⟩
  }

end BEDC.Derived.WritingItemAuditUp
