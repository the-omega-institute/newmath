import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_audit_index_readiness [AskSetup] [PackageSetup]
    {M A L I R H C P N exactRead ledgerRead markerRead indexRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont M A exactRead →
        Cont L R ledgerRead →
          Cont exactRead ledgerRead markerRead →
            Cont markerRead C indexRead →
              PkgSig bundle indexRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row indexRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row R ∨
                        hsame row exactRead ∨ hsame row ledgerRead ∨ hsame row markerRead ∨
                          hsame row indexRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M A exactRead ∧ Cont L R ledgerRead ∧
                        Cont exactRead ledgerRead markerRead ∧ Cont markerRead C indexRead ∧
                          PkgSig bundle indexRead pkg)
                    hsame ∧
                  UnaryHistory exactRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory markerRead ∧ UnaryHistory indexRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier exactRoute ledgerRoute markerRoute indexRoute indexPkg
  obtain ⟨mUnary, aUnary, lUnary, _iUnary, rUnary, _hUnary, cUnary, _pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed mUnary aUnary exactRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed lUnary rUnary ledgerRoute
  have markerUnary : UnaryHistory markerRead :=
    unary_cont_closed exactUnary ledgerUnary markerRoute
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed markerUnary cUnary indexRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row indexRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row R ∨
              hsame row exactRead ∨ hsame row ledgerRead ∨ hsame row markerRead ∨
                hsame row indexRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M A exactRead ∧ Cont L R ledgerRead ∧
              Cont exactRead ledgerRead markerRead ∧ Cont markerRead C indexRead ∧
                PkgSig bundle indexRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro indexRead ⟨hsame_refl indexRead, indexUnary⟩
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
      exact ⟨source.right, exactRoute, ledgerRoute, markerRoute, indexRoute, indexPkg⟩
  }
  exact ⟨cert, exactUnary, ledgerUnary, markerUnary, indexUnary, namePkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
