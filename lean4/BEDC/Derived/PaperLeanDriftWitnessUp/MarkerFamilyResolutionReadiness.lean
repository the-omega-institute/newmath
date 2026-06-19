import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_marker_family_resolution_readiness [AskSetup] [PackageSetup]
    {M A L I R H C P N familyRead verdictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont M A familyRead →
        Cont familyRead R verdictRead →
          PkgSig bundle verdictRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                    hsame row R ∨ hsame row verdictRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M A familyRead ∧
                    Cont familyRead R verdictRead ∧ PkgSig bundle verdictRead pkg)
                hsame ∧
              UnaryHistory familyRead ∧ UnaryHistory verdictRead ∧ Cont M A familyRead ∧
                Cont familyRead R verdictRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle verdictRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier familyRoute verdictRoute verdictPkg
  obtain ⟨mUnary, aUnary, _lUnary, _iUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    namePkg⟩ := carrier
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed mUnary aUnary familyRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed familyUnary rUnary verdictRoute
  have sourceAtVerdict : hsame verdictRead verdictRead ∧ UnaryHistory verdictRead :=
    ⟨hsame_refl verdictRead, verdictUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row verdictRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M A familyRead ∧ Cont familyRead R verdictRead ∧
              PkgSig bundle verdictRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro verdictRead sourceAtVerdict
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
      exact ⟨source.right, familyRoute, verdictRoute, verdictPkg⟩
  }
  exact ⟨cert, familyUnary, verdictUnary, familyRoute, verdictRoute, namePkg, verdictPkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
