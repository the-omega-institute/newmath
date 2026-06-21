import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierCriticalPairEnvelope [AskSetup] [PackageSetup]
    {P K J R S C B O H T G N criticalRead finiteRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier P K J R S C B O H T G N bundle pkg →
      Cont P K criticalRead →
        Cont J R finiteRead →
          Cont criticalRead finiteRead envelopeRead →
            PkgSig bundle envelopeRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row envelopeRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row K ∨ hsame row J ∨ hsame row R ∨
                      hsame row S ∨ hsame row C ∨ hsame row B ∨ hsame row O ∨
                        hsame row envelopeRead)
                  (fun row : BHist =>
                    hsame row envelopeRead ∧ Cont P K criticalRead ∧
                      Cont J R finiteRead ∧ Cont criticalRead finiteRead envelopeRead ∧
                        PkgSig bundle envelopeRead pkg)
                  hsame ∧
                UnaryHistory criticalRead ∧ UnaryHistory finiteRead ∧
                  UnaryHistory envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier criticalRoute finiteRoute envelopeRoute envelopePkg
  obtain ⟨pUnary, kUnary, jUnary, rUnary, _sUnary, _cUnary, _bUnary, _oUnary,
    _hUnary, _tUnary, _gUnary, _nUnary, _provenancePkg⟩ := carrier
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed pUnary kUnary criticalRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed jUnary rUnary finiteRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed criticalUnary finiteUnary envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row envelopeRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row P ∨ hsame row K ∨ hsame row J ∨ hsame row R ∨ hsame row S ∨
              hsame row C ∨ hsame row B ∨ hsame row O ∨ hsame row envelopeRead)
          (fun row : BHist =>
            hsame row envelopeRead ∧ Cont P K criticalRead ∧ Cont J R finiteRead ∧
              Cont criticalRead finiteRead envelopeRead ∧
                PkgSig bundle envelopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro envelopeRead ⟨hsame_refl envelopeRead, envelopeUnary, envelopePkg⟩
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, criticalRoute, finiteRoute, envelopeRoute, envelopePkg⟩
  }
  exact ⟨cert, criticalUnary, finiteUnary, envelopeUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
