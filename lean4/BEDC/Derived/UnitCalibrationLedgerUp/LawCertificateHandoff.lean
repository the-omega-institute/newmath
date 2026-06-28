import BEDC.Derived.UnitCalibrationLedgerUp.NameCertObligations

namespace BEDC.Derived.UnitCalibrationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UnitCalibrationLedgerCarrier_law_certificate_handoff [AskSetup] [PackageSetup]
    {measurement unitBridge calibration uncertainty instrument reproducibility dimension
      classifier transport provenance name lawRead auditRead truthRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnitCalibrationLedgerCarrier measurement unitBridge calibration uncertainty instrument
        reproducibility dimension classifier transport provenance name bundle pkg →
      Cont name provenance lawRead →
        Cont name provenance auditRead →
          Cont name provenance truthRead →
            PkgSig bundle lawRead pkg →
              PkgSig bundle auditRead pkg →
                PkgSig bundle truthRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row lawRead ∨ hsame row auditRead ∨ hsame row truthRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row measurement ∨ hsame row unitBridge ∨
                          hsame row calibration ∨ hsame row uncertainty ∨
                            hsame row instrument ∨ hsame row reproducibility ∨
                              hsame row dimension ∨ hsame row classifier ∨
                                hsame row transport ∨ hsame row provenance ∨
                                  hsame row name ∨ hsame row lawRead ∨
                                    hsame row auditRead ∨ hsame row truthRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧
                          UnitCalibrationLedgerCarrier measurement unitBridge calibration
                            uncertainty instrument reproducibility dimension classifier
                            transport provenance name bundle pkg ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle lawRead pkg ∧
                              PkgSig bundle auditRead pkg ∧ PkgSig bundle truthRead pkg)
                      hsame ∧
                    UnaryHistory lawRead ∧ UnaryHistory auditRead ∧ UnaryHistory truthRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrierData lawRoute auditRoute truthRoute lawPkg auditPkg truthPkg
  have carrierOriginal :
      UnitCalibrationLedgerCarrier measurement unitBridge calibration uncertainty instrument
        reproducibility dimension classifier transport provenance name bundle pkg := carrierData
  obtain ⟨_measurementUnary, _unitBridgeUnary, _calibrationUnary, _uncertaintyUnary,
    _instrumentUnary, _reproducibilityUnary, _dimensionUnary, _classifierUnary,
    _transportUnary, provenanceUnary, nameUnary, _measurementUnitClassifier,
    _transportSelf, provenancePkg, _namePkg⟩ := carrierData
  have lawUnary : UnaryHistory lawRead :=
    unary_cont_closed nameUnary provenanceUnary lawRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed nameUnary provenanceUnary auditRoute
  have truthUnary : UnaryHistory truthRead :=
    unary_cont_closed nameUnary provenanceUnary truthRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lawRead ∨ hsame row auditRead ∨ hsame row truthRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row measurement ∨ hsame row unitBridge ∨ hsame row calibration ∨
              hsame row uncertainty ∨ hsame row instrument ∨ hsame row reproducibility ∨
                hsame row dimension ∨ hsame row classifier ∨ hsame row transport ∨
                  hsame row provenance ∨ hsame row name ∨ hsame row lawRead ∨
                    hsame row auditRead ∨ hsame row truthRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              UnitCalibrationLedgerCarrier measurement unitBridge calibration uncertainty
                instrument reproducibility dimension classifier transport provenance name
                bundle pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle lawRead pkg ∧
                  PkgSig bundle auditRead pkg ∧ PkgSig bundle truthRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro lawRead ⟨Or.inl (hsame_refl lawRead), lawUnary⟩
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
        intro row other sameRows sourceRow
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameLaw =>
              exact Or.inl (lift sameLaw)
          | inr rest =>
              cases rest with
              | inl sameAudit =>
                  exact Or.inr (Or.inl (lift sameAudit))
              | inr sameTruth =>
                  exact Or.inr (Or.inr (lift sameTruth))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameLaw =>
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
                                (Or.inr (Or.inl sameLaw)))))))))))
      | inr rest =>
          cases rest with
          | inl sameAudit =>
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
                                    (Or.inr
                                      (Or.inr (Or.inl sameAudit))))))))))))
          | inr sameTruth =>
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
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr sameTruth))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, provenancePkg, lawPkg, auditPkg, truthPkg⟩
  }
  exact ⟨cert, lawUnary, auditUnary, truthUnary⟩

end BEDC.Derived.UnitCalibrationLedgerUp
