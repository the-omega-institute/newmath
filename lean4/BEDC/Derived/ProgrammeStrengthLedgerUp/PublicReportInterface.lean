import BEDC.Derived.ProgrammeStrengthLedgerUp.TasteGate

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProgrammeStrengthLedgerPublicReportInterface [AskSetup] [PackageSetup]
    {Q S D V B R H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProgrammeStrengthLedgerCarrier Q S D V B R H C P N bundle pkg →
      Cont C N publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row V ∨
                  hsame row B ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N publicRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier publicRoute publicPkg
  obtain ⟨_qUnary, _sUnary, _dUnary, _vUnary, _bUnary, _rUnary, _hUnary, cUnary,
    _pUnary, nUnary, _claimStrength, _dependencyStatus, _bridgeRefusal, provenancePkg,
    namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed cUnary nUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row V ∨
              hsame row B ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N publicRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, provenancePkg, namePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ProgrammeStrengthLedgerUp
