import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_audit_replay_source_lock [AskSetup] [PackageSetup]
    {M A L I R H C P N replayRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont R C replayRead ->
        Cont replayRead P exportRead ->
          PkgSig bundle exportRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row replayRead ∨ hsame row exportRead)
                (fun row : BHist => PkgSig bundle exportRead pkg ∧ hsame row exportRead)
                hsame ∧
              UnaryHistory replayRead ∧ UnaryHistory exportRead ∧ Cont R C replayRead ∧
                Cont replayRead P exportRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier replayRoute exportRoute exportPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, _hUnary, cUnary, pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed rUnary cUnary replayRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed replayUnary pUnary exportRoute
  have sourceAtExport : hsame exportRead exportRead ∧ UnaryHistory exportRead :=
    ⟨hsame_refl exportRead, exportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row replayRead ∨ hsame row exportRead)
          (fun row : BHist => PkgSig bundle exportRead pkg ∧ hsame row exportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead sourceAtExport
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨exportPkg, source.left⟩
  }
  exact ⟨cert, replayUnary, exportUnary, replayRoute, exportRoute, namePkg, exportPkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
