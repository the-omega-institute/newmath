import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScientificObjectEmpiricalBridgeSeparation [AskSetup] [PackageSetup]
    {L B O T D H ledgerRead bridgeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory B →
        UnaryHistory O →
          UnaryHistory T →
            UnaryHistory D →
              UnaryHistory H →
                Cont L B ledgerRead →
                  Cont B O bridgeRead →
                    PkgSig bundle ledgerRead pkg →
                      PkgSig bundle bridgeRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row L ∨ hsame row B ∨ hsame row ledgerRead ∨
                                hsame row bridgeRead)
                            (fun row : BHist =>
                              hsame row L ∨ hsame row B ∨ hsame row O ∨
                                hsame row T ∨ hsame row D ∨ hsame row H ∨
                                  hsame row ledgerRead ∨ hsame row bridgeRead)
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
                            hsame ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro lUnary bUnary _oUnary _tUnary _dUnary _hUnary ledgerRoute bridgeRoute ledgerPkg
    bridgePkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed lUnary bUnary ledgerRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed bUnary _oUnary bridgeRoute
  have source :
      (fun row : BHist =>
        hsame row L ∨ hsame row B ∨ hsame row ledgerRead ∨ hsame row bridgeRead) L := by
    exact Or.inl (hsame_refl L)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row L ∨ hsame row B ∨ hsame row ledgerRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            hsame row L ∨ hsame row B ∨ hsame row O ∨ hsame row T ∨ hsame row D ∨
              hsame row H ∨ hsame row ledgerRead ∨ hsame row bridgeRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro L source
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
        intro _row _other sameRows rowSource
        cases rowSource with
        | inl sameLedger =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)
        | inr rest =>
            cases rest with
            | inl sameBridge =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBridge))
            | inr rest =>
                cases rest with
                | inl sameLedgerRead =>
                    exact
                      Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameLedgerRead)))
                | inr sameBridgeRead =>
                    exact
                      Or.inr (Or.inr (Or.inr
                        (hsame_trans (hsame_symm sameRows) sameBridgeRead)))
    }
    pattern_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameLedger =>
          exact Or.inl sameLedger
      | inr rest =>
          cases rest with
          | inl sameBridge =>
              exact Or.inr (Or.inl sameBridge)
          | inr rest =>
              cases rest with
              | inl sameLedgerRead =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl sameLedgerRead))))))
              | inr sameBridgeRead =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr sameBridgeRead))))))
    ledger_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameLedger =>
          exact ⟨unary_transport lUnary (hsame_symm sameLedger), bridgePkg⟩
      | inr rest =>
          cases rest with
          | inl sameBridge =>
              exact ⟨unary_transport bUnary (hsame_symm sameBridge), bridgePkg⟩
          | inr rest =>
              cases rest with
              | inl sameLedgerRead =>
                  exact
                    ⟨unary_transport ledgerUnary (hsame_symm sameLedgerRead), bridgePkg⟩
              | inr sameBridgeRead =>
                  exact
                    ⟨unary_transport bridgeUnary (hsame_symm sameBridgeRead), bridgePkg⟩
  }
  exact ⟨cert, ledgerUnary, bridgeUnary⟩

end BEDC.Derived.ScientificObjectUp
