import BEDC.Derived.RealityConstrainedTruthCertUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedTruthCertClassifier_row_certificate [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N S' Sigma' K' T' U' D' I' L' F' N'
      classifierRead ledgerRead failureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      RealityConstrainedTruthCertClassifier S Sigma K T U D I L F N S' Sigma' K' T'
          U' D' I' L' F' N' ->
        Cont K K' classifierRead ->
          Cont L L' ledgerRead ->
            Cont F F' failureRead ->
              PkgSig bundle classifierRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  PkgSig bundle failureRead pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          UnaryHistory row ∧
                            (hsame row classifierRead ∨ hsame row ledgerRead ∨
                              hsame row failureRead))
                        (fun row : BHist =>
                          UnaryHistory row ∧
                            (hsame row classifierRead ∨ hsame row ledgerRead ∨
                              hsame row failureRead))
                        (fun row : BHist =>
                          (hsame row classifierRead ∧ PkgSig bundle classifierRead pkg) ∨
                            (hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg) ∨
                              (hsame row failureRead ∧ PkgSig bundle failureRead pkg))
                        hsame ∧
                      UnaryHistory classifierRead ∧
                        UnaryHistory ledgerRead ∧ UnaryHistory failureRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier classifierSame classifierRoute ledgerRoute failureRoute classifierPkg ledgerPkg
    failurePkg
  obtain ⟨sourceUnary, signatureUnary, _towerUnary, _stabilityUnary, invariantUnary,
    ledgerUnary, sourceRoute, _towerRoute, invariantRoute, _nameRoute⟩ := carrier
  obtain ⟨_sameSource, _sameSignature, sameClassifier, _sameTower, _sameStability,
    _sameDescent, _sameInvariant, sameLedger, sameFailure, _sameName⟩ := classifierSame
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceRoute
  have classifierUnary' : UnaryHistory K' :=
    unary_transport classifierUnary sameClassifier
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have failureUnary' : UnaryHistory F' :=
    unary_transport failureUnary sameFailure
  have ledgerUnary' : UnaryHistory L' :=
    unary_transport ledgerUnary sameLedger
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed classifierUnary classifierUnary' classifierRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary ledgerUnary' ledgerRoute
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed failureUnary failureUnary' failureRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row classifierRead ∨ hsame row ledgerRead ∨ hsame row failureRead))
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row classifierRead ∨ hsame row ledgerRead ∨ hsame row failureRead))
        (fun row : BHist =>
          (hsame row classifierRead ∧ PkgSig bundle classifierRead pkg) ∨
            (hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg) ∨
              (hsame row failureRead ∧ PkgSig bundle failureRead pkg))
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro classifierRead
            ⟨classifierReadUnary, Or.inl (hsame_refl classifierRead)⟩
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
          constructor
          · exact unary_transport source.left sameRows
          · cases source.right with
            | inl classifierSameRow =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) classifierSameRow)
            | inr rest =>
                cases rest with
                | inl ledgerSameRow =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) ledgerSameRow))
                | inr failureSameRow =>
                    exact Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) failureSameRow))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        cases source.right with
        | inl classifierSameRow =>
            exact Or.inl ⟨classifierSameRow, classifierPkg⟩
        | inr rest =>
            cases rest with
            | inl ledgerSameRow =>
                exact Or.inr (Or.inl ⟨ledgerSameRow, ledgerPkg⟩)
            | inr failureSameRow =>
                exact Or.inr (Or.inr ⟨failureSameRow, failurePkg⟩)
    }
  exact ⟨cert, classifierReadUnary, ledgerReadUnary, failureReadUnary⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
