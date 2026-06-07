import BEDC.Derived.ParsevalUp.NameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootOrthogonalityLedger [AskSetup] [PackageSetup]
    {F S I E R D L H C P N orthogonalityRead energyRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F ->
      UnaryHistory S ->
        UnaryHistory I ->
          UnaryHistory E ->
            UnaryHistory R ->
              UnaryHistory D ->
                UnaryHistory L ->
                  Cont F S orthogonalityRead ->
                    Cont orthogonalityRead I energyRead ->
                      Cont energyRead D toleranceRead ->
                        Cont toleranceRead L sealRead ->
                          hsame H (append C P) ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row F ∨ hsame row S ∨
                                        hsame row orthogonalityRead ∨ hsame row I ∨
                                          hsame row energyRead ∨ hsame row E ∨
                                            hsame row R ∨ hsame row D ∨
                                              hsame row toleranceRead ∨ hsame row L ∨
                                                hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont F S orthogonalityRead ∧
                                          Cont orthogonalityRead I energyRead ∧
                                            Cont energyRead D toleranceRead ∧
                                              Cont toleranceRead L sealRead ∧
                                                hsame H (append C P) ∧
                                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧ UnaryHistory orthogonalityRead ∧
                                  UnaryHistory energyRead ∧ UnaryHistory toleranceRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ParsevalUp BHist ProbeBundle Pkg Cont PkgSig append hsame SemanticNameCert UnaryHistory
  intro fourierUnary sourceUnary pairingUnary _integralUnary _readbackUnary toleranceUnary sealUnary
  intro orthogonalityRoute energyRoute toleranceRoute sealRoute provenanceAnchor provenancePkg namePkg
  have orthogonalityUnary : UnaryHistory orthogonalityRead :=
    unary_cont_closed fourierUnary sourceUnary orthogonalityRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed orthogonalityUnary pairingUnary energyRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed energyUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row orthogonalityRead ∨ hsame row I ∨
              hsame row energyRead ∨ hsame row E ∨ hsame row R ∨ hsame row D ∨
                hsame row toleranceRead ∨ hsame row L ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S orthogonalityRead ∧
              Cont orthogonalityRead I energyRead ∧ Cont energyRead D toleranceRead ∧
                Cont toleranceRead L sealRead ∧ hsame H (append C P) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact
        ⟨source.right, orthogonalityRoute, energyRoute, toleranceRoute, sealRoute,
          provenanceAnchor, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, orthogonalityUnary, energyUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.ParsevalUp
