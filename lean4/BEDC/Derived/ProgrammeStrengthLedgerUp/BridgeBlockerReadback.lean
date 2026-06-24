import BEDC.Derived.ProgrammeStrengthLedgerUp.PublicReportInterface

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProgrammeStrengthLedgerBridgeBlockerReadback [AskSetup] [PackageSetup]
    {Q S D V B R H C P N blockerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProgrammeStrengthLedgerCarrier Q S D V B R H C P N bundle pkg ->
      Cont B D blockerRead ->
        PkgSig bundle blockerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row blockerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Q ∨ hsame row B ∨ hsame row D ∨ hsame row blockerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont B D blockerRead ∧ PkgSig bundle blockerRead pkg)
              hsame ∧
            PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier blockerRoute blockerPkg
  obtain ⟨_qUnary, _sUnary, dUnary, _vUnary, bUnary, _rUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _claimStrength, _dependencyStatus, _bridgeRefusal, provenancePkg,
    _namePkg⟩ := carrier
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed bUnary dUnary blockerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row blockerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row B ∨ hsame row D ∨ hsame row blockerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B D blockerRead ∧ PkgSig bundle blockerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro blockerRead ⟨hsame_refl blockerRead, blockerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, blockerRoute, blockerPkg⟩
  }
  exact ⟨cert, provenancePkg⟩

end BEDC.Derived.ProgrammeStrengthLedgerUp
