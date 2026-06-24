import BEDC.Derived.AnalogyCertificateGateUp.NameCertObligations

namespace BEDC.Derived.AnalogyCertificateGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalogyCertificateGateIndependenceWitness [AskSetup] [PackageSetup]
    {sourceRows carrierRow classifierRow relationRows preservedRows refusedRows ledgerRow
      exactnessRow failureRow transport replay provenance localName witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalogyCertificateGateCarrier sourceRows carrierRow classifierRow relationRows preservedRows
        refusedRows ledgerRow exactnessRow failureRow transport replay provenance localName
        bundle pkg →
      Cont failureRow localName witnessRead →
        PkgSig bundle witnessRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceRows ∨ hsame row carrierRow ∨ hsame row classifierRow ∨
                  hsame row relationRows ∨ hsame row preservedRows ∨
                    hsame row refusedRows ∨ hsame row ledgerRow ∨
                      hsame row exactnessRow ∨ hsame row failureRow ∨
                        hsame row witnessRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle witnessRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier failureLocal witnessPkg
  obtain ⟨_sourceUnary, _carrierUnary, _classifierUnary, _relationUnary, preservedUnary,
    refusedUnary, ledgerUnary, exactnessUnary, failureUnary, _transportUnary, _replayUnary,
    provenanceUnary, localUnary, preservedRefusedLedger, ledgerExactnessFailure,
    provenancePkg, _localPkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed failureUnary localUnary failureLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRows ∨ hsame row carrierRow ∨ hsame row classifierRow ∨
              hsame row relationRows ∨ hsame row preservedRows ∨ hsame row refusedRows ∨
                hsame row ledgerRow ∨ hsame row exactnessRow ∨ hsame row failureRow ∨
                  hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle witnessRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, witnessPkg, provenancePkg⟩
  }
  exact ⟨cert, witnessUnary⟩

end BEDC.Derived.AnalogyCertificateGateUp
