import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCommonTailWindowClassifier [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert tailWindow2
      modulus2 tolerance2 ledger2 sealRow2 transport2 routes2 provenance2 nameCert2
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      CauchyOscillationCarrier tailWindow2 modulus2 tolerance2 ledger2 sealRow2 transport2
        routes2 provenance2 nameCert2 bundle pkg ->
        hsame tailWindow tailWindow2 ->
          hsame modulus modulus2 ->
            hsame tolerance tolerance2 ->
              hsame ledger ledger2 ->
                hsame sealRow sealRow2 ->
                  Cont tailWindow tailWindow2 classifierRead ->
                    PkgSig bundle classifierRead pkg ->
                      SemanticNameCert
                            (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row tailWindow ∨ hsame row tailWindow2 ∨
                                hsame row modulus ∨ hsame row modulus2 ∨
                                  hsame row tolerance ∨ hsame row tolerance2 ∨
                                    hsame row ledger ∨ hsame row ledger2 ∨
                                      hsame row sealRow ∨ hsame row sealRow2 ∨
                                        hsame row classifierRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ hsame tailWindow tailWindow2 ∧
                                hsame modulus modulus2 ∧ hsame tolerance tolerance2 ∧
                                  hsame ledger ledger2 ∧ hsame sealRow sealRow2 ∧
                                    Cont tailWindow tailWindow2 classifierRead ∧
                                      PkgSig bundle classifierRead pkg)
                            hsame ∧
                        UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrierLeft carrierRight sameTail sameModulus sameTolerance sameLedger sameSeal
    classifierRoute classifierPkg
  obtain ⟨tailUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, _provenancePkg⟩ := carrierLeft
  obtain ⟨tailUnary2, _modulusUnary2, _toleranceUnary2, _ledgerUnary2, _sealUnary2,
    _transportUnary2, _routesUnary2, _provenanceUnary2, _nameCertUnary2,
    _tailWindowModulus2, _modulusTolerance2, _ledgerSeal2, _routesNameCert2,
    _provenancePkg2⟩ := carrierRight
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed tailUnary tailUnary2 classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row tailWindow2 ∨ hsame row modulus ∨
              hsame row modulus2 ∨ hsame row tolerance ∨ hsame row tolerance2 ∨
                hsame row ledger ∨ hsame row ledger2 ∨ hsame row sealRow ∨
                  hsame row sealRow2 ∨ hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame tailWindow tailWindow2 ∧ hsame modulus modulus2 ∧
              hsame tolerance tolerance2 ∧ hsame ledger ledger2 ∧ hsame sealRow sealRow2 ∧
                Cont tailWindow tailWindow2 classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sameTail, sameModulus, sameTolerance, sameLedger, sameSeal,
          classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, classifierUnary⟩

end BEDC.Derived.CauchyOscillationUp
