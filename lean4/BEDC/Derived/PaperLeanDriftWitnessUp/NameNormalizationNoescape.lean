import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_name_normalization_noescape [AskSetup] [PackageSetup]
    {M A L I R H C P N normalized replayed verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont A H normalized →
        Cont normalized C replayed →
          Cont replayed I verdict →
            PkgSig bundle P pkg →
              PkgSig bundle verdict pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row verdict ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                        hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row normalized ∨ hsame row replayed ∨
                            hsame row verdict)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A H normalized ∧
                        Cont normalized C replayed ∧ Cont replayed I verdict ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle verdict pkg)
                    hsame ∧
                  UnaryHistory normalized ∧ UnaryHistory replayed ∧
                    UnaryHistory verdict := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier normalizeRoute replayRoute verdictRoute pkgP verdictPkg
  obtain
    ⟨_mUnary, aUnary, _lUnary, iUnary, _rUnary, hUnary, cUnary, _pUnary,
      _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
      _namePkg⟩ := carrier
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed aUnary hUnary normalizeRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed normalizedUnary cUnary replayRoute
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed replayedUnary iUnary verdictRoute
  have sourceVerdict :
      (fun row : BHist => hsame row verdict ∧ UnaryHistory row) verdict := by
    exact ⟨hsame_refl verdict, verdictUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row verdict ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row normalized ∨ hsame row replayed ∨
                  hsame row verdict)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A H normalized ∧ Cont normalized C replayed ∧
              Cont replayed I verdict ∧ PkgSig bundle P pkg ∧
                PkgSig bundle verdict pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro verdict sourceVerdict
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
      repeat first
        | apply Or.inr
        | exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, normalizeRoute, replayRoute, verdictRoute, pkgP, verdictPkg⟩
  }
  exact ⟨cert, normalizedUnary, replayedUnary, verdictUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
