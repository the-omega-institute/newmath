import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_objectwise_drift_handoff [AskSetup] [PackageSetup]
    {M A L I R H C P N exactRead duplicateRead verdictRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont L I exactRead ->
        Cont M L duplicateRead ->
          Cont exactRead duplicateRead verdictRead ->
            Cont verdictRead H handoffRead ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                        hsame row R ∨ hsame row exactRead ∨ hsame row duplicateRead ∨
                          hsame row verdictRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont L I exactRead ∧
                        Cont M L duplicateRead ∧
                          Cont exactRead duplicateRead verdictRead ∧
                            Cont verdictRead H handoffRead ∧ PkgSig bundle handoffRead pkg)
                    hsame ∧
                  UnaryHistory exactRead ∧ UnaryHistory duplicateRead ∧
                    UnaryHistory verdictRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier exactRoute duplicateRoute verdictRoute handoffRoute handoffPkg
  obtain ⟨mUnary, _aUnary, lUnary, iUnary, _rUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed lUnary iUnary exactRoute
  have duplicateUnary : UnaryHistory duplicateRead :=
    unary_cont_closed mUnary lUnary duplicateRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed exactUnary duplicateUnary verdictRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed verdictUnary hUnary handoffRoute
  have sourceAtHandoff : hsame handoffRead handoffRead ∧ UnaryHistory handoffRead :=
    ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row exactRead ∨ hsame row duplicateRead ∨
                hsame row verdictRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L I exactRead ∧ Cont M L duplicateRead ∧
              Cont exactRead duplicateRead verdictRead ∧ Cont verdictRead H handoffRead ∧
                PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceAtHandoff
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, exactRoute, duplicateRoute, verdictRoute, handoffRoute,
          handoffPkg⟩
  }
  exact ⟨cert, exactUnary, duplicateUnary, verdictUnary, handoffUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
