import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_overlap_classifier_route_certificate
    [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      overlapRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      Cont source leftOverlap overlapRead ->
        Cont overlapRead witness classifierRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row classifierRead ∧
                  Cont source leftOverlap overlapRead)
                (fun row : BHist => hsame row classifierRead ∧
                  Cont overlapRead witness classifierRead)
                hsame ∧
              UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
                UnaryHistory overlapRead ∧ UnaryHistory classifierRead ∧
                  Cont source leftOverlap overlapRead ∧
                    Cont overlapRead witness classifierRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro carrier sourceLeftOverlapRead overlapWitnessClassifier classifierReadPkg
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, _operationUnary, _outputUnary,
    _branchUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, _provenancePkg, namePkg⟩ :=
      carrier
  have overlapReadUnary : UnaryHistory overlapRead :=
    unary_cont_closed sourceUnary leftOverlapUnary sourceLeftOverlapRead
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed overlapReadUnary witnessUnary overlapWitnessClassifier
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row classifierRead ∧ Cont source leftOverlap overlapRead)
        (fun row : BHist => hsame row classifierRead ∧
          Cont overlapRead witness classifierRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        (And.intro (hsame_refl classifierRead) classifierReadUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left)
          (unary_transport sourceRow.right same)
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left sourceLeftOverlapRead
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left overlapWitnessClassifier
  }
  exact
    ⟨cert, sourceUnary, leftOverlapUnary, witnessUnary, overlapReadUnary,
      classifierReadUnary, sourceLeftOverlapRead, overlapWitnessClassifier, namePkg,
      classifierReadPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
