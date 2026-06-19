import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp.ConsumerRowScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_consumer_row_scope [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead replayRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        Cont verdictRead C replayRead →
          Cont replayRead P consumerRead →
            PkgSig bundle consumerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                      hsame row R ∨ hsame row verdictRead ∨ hsame row replayRead ∨
                        hsame row consumerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R H verdictRead ∧
                      Cont verdictRead C replayRead ∧
                        Cont replayRead P consumerRead ∧ PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory verdictRead ∧ UnaryHistory replayRead ∧
                  UnaryHistory consumerRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier verdictRoute replayRoute consumerRoute consumerPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, hUnary, cUnary, pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed verdictUnary cUnary replayRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed replayUnary pUnary consumerRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row verdictRead ∨ hsame row replayRead ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R H verdictRead ∧ Cont verdictRead C replayRead ∧
              Cont replayRead P consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, verdictRoute, replayRoute, consumerRoute, consumerPkg⟩
  }
  exact ⟨cert, verdictUnary, replayUnary, consumerUnary, namePkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp.ConsumerRowScope
