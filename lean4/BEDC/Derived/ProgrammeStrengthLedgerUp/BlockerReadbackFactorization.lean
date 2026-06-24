import BEDC.Derived.ProgrammeStrengthLedgerUp.BridgeBlockerReadback

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProgrammeStrengthLedgerBlockerReadbackFactorization [AskSetup] [PackageSetup]
    {Q S D V B R H C P N blockerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProgrammeStrengthLedgerCarrier Q S D V B R H C P N bundle pkg →
      Cont B D blockerRead →
        Cont blockerRead C publicRead →
          PkgSig bundle blockerRead pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row blockerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row D ∨ hsame row B ∨ hsame row blockerRead ∨
                      hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B D blockerRead ∧ Cont blockerRead C publicRead ∧
                      PkgSig bundle blockerRead pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory blockerRead ∧
                  UnaryHistory publicRead ∧
                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier blockerRoute publicRoute blockerPkg publicPkg
  obtain ⟨_qUnary, _sUnary, dUnary, _vUnary, bUnary, _rUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _claimStrength, _dependencyStatus, _bridgeRefusal, provenancePkg,
    _namePkg⟩ := carrier
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed bUnary dUnary blockerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed blockerUnary cUnary publicRoute
  have sourceAtBlocker :
      (fun row : BHist => hsame row blockerRead ∧ UnaryHistory row) blockerRead :=
    ⟨hsame_refl blockerRead, blockerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row blockerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row D ∨ hsame row B ∨ hsame row blockerRead ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B D blockerRead ∧ Cont blockerRead C publicRead ∧
              PkgSig bundle blockerRead pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro blockerRead sourceAtBlocker
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, blockerRoute, publicRoute, blockerPkg, publicPkg⟩
  }
  exact ⟨cert, blockerUnary, publicUnary, provenancePkg⟩

end BEDC.Derived.ProgrammeStrengthLedgerUp
