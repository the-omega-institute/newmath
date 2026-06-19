import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_resolution_consumer_readiness [AskSetup] [PackageSetup]
    {M A L I R H C P N exactRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont M A exactRead →
        Cont exactRead R consumerRead →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M A exactRead ∧
                    Cont exactRead R consumerRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle consumerRead pkg)
                hsame ∧
              UnaryHistory exactRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier exactRoute consumerRoute consumerPkg
  obtain ⟨mUnary, aUnary, _lUnary, _iUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed mUnary aUnary exactRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed exactUnary rUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M A exactRead ∧ Cont exactRead R consumerRead ∧
              PkgSig bundle N pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exactRoute, consumerRoute, namePkg, consumerPkg⟩
  }
  exact ⟨cert, exactUnary, consumerUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
