import BEDC.Derived.ParsevalUp.NameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootIntegralRegSeqRatHandoff [AskSetup] [PackageSetup]
    {F S I E R D L H C P N integralRead readbackRead toleranceRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrierSurface F S I E R D L H C P N bundle pkg →
      Cont I E integralRead →
        Cont integralRead R readbackRead →
          Cont readbackRead D toleranceRead →
            Cont toleranceRead L sealRead →
              Cont sealRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row E ∨ hsame row R ∨ hsame row D ∨
                          hsame row L ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont I E integralRead ∧
                          Cont integralRead R readbackRead ∧
                            Cont readbackRead D toleranceRead ∧
                              Cont toleranceRead L sealRead ∧
                                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory integralRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ParsevalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier integralRoute readbackRoute toleranceRoute sealRoute namedRoute namedPkg
  obtain ⟨_fourierUnary, _sourceUnary, pairingUnary, integralUnary, readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed pairingUnary integralUnary integralRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed integralReadUnary readbackUnary readbackRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackReadUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row E ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I E integralRead ∧
              Cont integralRead R readbackRead ∧ Cont readbackRead D toleranceRead ∧
                Cont toleranceRead L sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact
        ⟨source.right, integralRoute, readbackRoute, toleranceRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact
    ⟨cert, integralReadUnary, readbackReadUnary, toleranceReadUnary, sealReadUnary,
      namedReadUnary⟩

end BEDC.Derived.ParsevalUp
