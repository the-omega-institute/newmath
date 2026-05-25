import BEDC.Derived.UniformCompletionUp.TasteGate

namespace BEDC.Derived.UniformCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

namespace TasteGate

theorem UniformCompletion_directed_net_witness_certificate [AskSetup] [PackageSetup]
    {F D U E H C P N witnessRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionCarrier N →
      Cont F D witnessRead →
        Cont witnessRead U exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UniformCompletionCarrier N)
                (fun row : BHist =>
                  hsame row F ∨ hsame row D ∨ hsame row witnessRead ∨
                    hsame row exportRead)
                (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                UniformCompletionClassifier ∧
              UniformCompletionCauchyFilterPattern N ∧
                UniformCompletionLedgerPolicy N ∧
                  Exists (fun route : BHist => Cont F D route) := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro carrier witnessRoute _exportRoute exportPkg
  have carrierPacket : UniformCompletionCarrier N := carrier
  obtain ⟨F0, D0, U0, E0, H0, C0, P0, N0, sameName, filterRoute,
    extensionRoute, replayRoute, ledgerRoute⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UniformCompletionCarrier N)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row witnessRead ∨ hsame row exportRead)
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
          intro _row _other sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact
    ⟨cert,
      ⟨F0, D0, U0, filterRoute, E0, H0, C0, P0, N0, sameName, extensionRoute,
        replayRoute, ledgerRoute⟩,
      ⟨P0, N0, sameName, ledgerRoute⟩,
      ⟨witnessRead, witnessRoute⟩⟩

end TasteGate

end BEDC.Derived.UniformCompletionUp
