import BEDC.Derived.UniformCompletionUp.TasteGate

namespace BEDC.Derived.UniformCompletionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

theorem UniformCompletion_public_factorization [AskSetup] [PackageSetup]
    {F D U E H C P N directedRead extensionRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionCarrier N →
      Cont F D directedRead →
        Cont directedRead U extensionRead →
          Cont P realRead N →
            Cont extensionRead realRead publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UniformCompletionCarrier N)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row D ∨ hsame row U ∨ hsame row E ∨
                        hsame row directedRead ∨ hsame row extensionRead ∨
                          hsame row realRead ∨ hsame row publicRead)
                    (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                    UniformCompletionClassifier ∧
                  UniformCompletionCauchyFilterPattern N ∧
                    UniformCompletionLedgerPolicy N := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier _directedRoute _extensionRoute _realRoute _publicRoute publicPkg
  have carrierPacket : UniformCompletionCarrier N := carrier
  obtain ⟨F0, D0, U0, E0, H0, C0, P0, N0, sameName, filterRoute,
    carrierExtensionRoute, replayRoute, ledgerRoute⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UniformCompletionCarrier N)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row U ∨ hsame row E ∨
              hsame row directedRead ∨ hsame row extensionRead ∨
                hsame row realRead ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          UniformCompletionClassifier := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, carrierPacket⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, publicPkg⟩
    }
  exact
    ⟨cert,
      ⟨F0, D0, U0, filterRoute, E0, H0, C0, P0, N0, sameName,
        carrierExtensionRoute, replayRoute, ledgerRoute⟩,
      ⟨P0, N0, sameName, ledgerRoute⟩⟩

theorem UniformCompletion_extension_comparison_certificate [AskSetup] [PackageSetup]
    {F D U E H C P N extensionRead comparisonRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionCarrier N →
      Cont F D U →
        Cont U E extensionRead →
          Cont extensionRead comparisonRead exportRead →
            PkgSig bundle exportRead pkg →
              hsame comparisonRead E →
                SemanticNameCert
                    (fun row : BHist => hsame row exportRead ∧ UniformCompletionCarrier N)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row D ∨ hsame row U ∨ hsame row E ∨
                        hsame row extensionRead ∨ hsame row comparisonRead ∨
                          hsame row exportRead)
                    (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                    UniformCompletionClassifier ∧
                  UniformCompletionCauchyFilterPattern N ∧
                    UniformCompletionLedgerPolicy N ∧
                      UniformCompletionClassifier comparisonRead E := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier _filterDisplay _extensionDisplay _exportRoute exportPkg sameComparison
  have carrierPacket : UniformCompletionCarrier N := carrier
  obtain ⟨F0, D0, U0, E0, H0, C0, P0, N0, sameName, filterRoute,
    extensionRoute, replayRoute, ledgerRoute⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UniformCompletionCarrier N)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row U ∨ hsame row E ∨
              hsame row extensionRead ∨ hsame row comparisonRead ∨
                hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
          UniformCompletionClassifier := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, carrierPacket⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportPkg⟩
    }
  exact
    ⟨cert,
      ⟨F0, D0, U0, filterRoute, E0, H0, C0, P0, N0, sameName, extensionRoute,
        replayRoute, ledgerRoute⟩,
      ⟨P0, N0, sameName, ledgerRoute⟩,
      sameComparison⟩

theorem UniformCompletion_extension_scope_regseqrat_handoff
    {F D U E H C P N regRead realRead : BHist} :
    UniformCompletionCarrier N →
      Cont F D U →
        Cont U E H →
          Cont P regRead realRead →
            hsame regRead P →
              UniformCompletionCauchyFilterPattern N ∧
                UniformCompletionLedgerPolicy N ∧
                  UniformCompletionClassifier regRead P ∧
                    Exists (fun route : BHist => Cont U E route) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  intro carrier displayedFilter displayedExtension _realRoute sameRegRead
  obtain ⟨F0, D0, U0, E0, H0, C0, P0, N0, sameName, filterRoute,
    extensionRoute, replayRoute, ledgerRoute⟩ := carrier
  exact
    ⟨⟨F0, D0, U0, filterRoute, E0, H0, C0, P0, N0, sameName, extensionRoute,
        replayRoute, ledgerRoute⟩,
      ⟨P0, N0, sameName, ledgerRoute⟩,
      sameRegRead,
      ⟨H, displayedExtension⟩⟩

end TasteGate
end BEDC.Derived.UniformCompletionUp
