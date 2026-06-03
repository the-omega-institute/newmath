import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationRegSeqRatRealNonescape [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert regseqRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont tailWindow modulus tolerance ->
        Cont modulus tolerance regseqRead ->
          Cont regseqRead sealRow sealRead ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                        hsame row regseqRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont modulus tolerance regseqRead ∧
                        Cont regseqRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory regseqRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier _tailModulus regseqRoute sealRoute provenancePkg sealPkg
  obtain ⟨_tailUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealRowUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierTailModulus,
    _carrierModulusTolerance, _carrierLedgerSeal, _carrierRoutesNameCert,
    _carrierProvenancePkg⟩ := carrier
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed modulusUnary toleranceUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealRowUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row regseqRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus tolerance regseqRead ∧
              Cont regseqRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regseqRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, regseqUnary, sealUnary⟩

end BEDC.Derived.CauchyOscillationUp
