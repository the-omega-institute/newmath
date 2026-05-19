import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_overlap_classifier_route [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      overlapRead operationRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch transport
        continuation provenance name bundle pkg →
      hsame overlapRead witness →
        Cont overlapRead operation operationRead →
          Cont operationRead continuation outputRead →
            PkgSig bundle outputRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row overlapRead ∨ hsame row operationRead ∨ hsame row outputRead)
                  (fun _row : BHist =>
                    Cont source leftOverlap witness ∧
                      Cont overlapRead operation operationRead ∧
                        Cont operationRead continuation outputRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle provenance pkg ∨ PkgSig bundle outputRead pkg))
                  hsame ∧
                UnaryHistory overlapRead ∧ UnaryHistory operationRead ∧
                  UnaryHistory outputRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier sameOverlapWitness overlapOperationRead operationContinuationOutput
    outputReadPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    _branchUnary, _transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    sourceLeftOverlapWitness, _witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have overlapReadUnary : UnaryHistory overlapRead :=
    unary_transport witnessUnary (hsame_symm sameOverlapWitness)
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed overlapReadUnary operationUnary overlapOperationRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed operationReadUnary continuationUnary operationContinuationOutput
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row overlapRead ∨ hsame row operationRead ∨ hsame row outputRead)
          (fun _row : BHist =>
            Cont source leftOverlap witness ∧ Cont overlapRead operation operationRead ∧
              Cont operationRead continuation outputRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle outputRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro overlapRead (Or.inl (hsame_refl overlapRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases source with
        | inl sameOverlap =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameOverlap)
        | inr rest =>
            cases rest with
            | inl sameOperation =>
                exact
                  Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOperation))
            | inr sameOutput =>
                exact
                  Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameOutput))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨sourceLeftOverlapWitness, overlapOperationRead, operationContinuationOutput⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameOverlap =>
          exact
            ⟨unary_transport overlapReadUnary (hsame_symm sameOverlap),
              Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameOperation =>
              exact
                ⟨unary_transport operationReadUnary (hsame_symm sameOperation),
                  Or.inl provenancePkg⟩
          | inr sameOutput =>
              exact
                ⟨unary_transport outputReadUnary (hsame_symm sameOutput),
                  Or.inr outputReadPkg⟩
  }
  exact
    ⟨cert, overlapReadUnary, operationReadUnary, outputReadUnary, provenancePkg,
      outputReadPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
