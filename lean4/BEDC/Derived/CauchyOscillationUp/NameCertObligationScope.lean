import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationNameCertObligationScope [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg →
      PkgSig bundle nameCert pkg →
        SemanticNameCert
          (fun row : BHist =>
            hsame row nameCert ∧
              CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
                provenance nameCert bundle pkg)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus tolerance ∧
              Cont modulus tolerance ledger ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg)
          hsame := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier nameCertPkg
  have carrierRows :
      CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg :=
    carrier
  obtain ⟨_tailWindowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary,
    _sealUnary, _transportUnary, _routesUnary, _provenanceUnary, nameCertUnary,
    tailWindowModulus, modulusTolerance, _ledgerSeal, _routesNameCert,
    provenancePkg⟩ := carrier
  have sourceName :
      (fun row : BHist =>
        hsame row nameCert ∧
          CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
            provenance nameCert bundle pkg) nameCert := by
    exact ⟨hsame_refl nameCert, carrierRows⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameCert ∧
              CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
                provenance nameCert bundle pkg)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus tolerance ∧
              Cont modulus tolerance ledger ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameCert sourceName
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm nameCertUnary source.left, tailWindowModulus,
          modulusTolerance, provenancePkg, nameCertPkg⟩
  }
  exact cert

end BEDC.Derived.CauchyOscillationUp
