import BEDC.Derived.ProgrammeStrengthLedgerUp.BridgeBlockerReadback

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProgrammeStrengthLedgerFormalTargetRequest [AskSetup] [PackageSetup]
    {Q S D V B R H C P N publicRead blockerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProgrammeStrengthLedgerCarrier Q S D V B R H C P N bundle pkg ->
      Cont C N publicRead ->
        Cont B D blockerRead ->
          PkgSig bundle publicRead pkg ->
            PkgSig bundle blockerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row publicRead ∨ hsame row blockerRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row V ∨
                      hsame row B ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row publicRead ∨
                          hsame row blockerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont C N publicRead ∧ Cont B D blockerRead ∧
                      PkgSig bundle publicRead pkg ∧ PkgSig bundle blockerRead pkg)
                  hsame ∧
                UnaryHistory publicRead ∧ UnaryHistory blockerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier publicRoute blockerRoute publicPkg blockerPkg
  obtain ⟨_qUnary, _sUnary, dUnary, _vUnary, bUnary, _rUnary, _hUnary, cUnary,
    _pUnary, nUnary, _claimStrength, _dependencyStatus, _bridgeRefusal, _provenancePkg,
    _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed cUnary nUnary publicRoute
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed bUnary dUnary blockerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row publicRead ∨ hsame row blockerRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row D ∨ hsame row V ∨ hsame row B ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead ∨ hsame row blockerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N publicRead ∧ Cont B D blockerRead ∧
              PkgSig bundle publicRead pkg ∧ PkgSig bundle blockerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨Or.inl (hsame_refl publicRead), publicUnary⟩
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
        cases source.left with
        | inl samePublic =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) samePublic),
                unary_transport source.right sameRows⟩
        | inr sameBlocker =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameBlocker),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl samePublic =>
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
                              (Or.inr
                                (Or.inl samePublic))))))))))
      | inr sameBlocker =>
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
                              (Or.inr
                                (Or.inr sameBlocker))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, blockerRoute, publicPkg, blockerPkg⟩
  }
  exact ⟨cert, publicUnary, blockerUnary⟩

end BEDC.Derived.ProgrammeStrengthLedgerUp
