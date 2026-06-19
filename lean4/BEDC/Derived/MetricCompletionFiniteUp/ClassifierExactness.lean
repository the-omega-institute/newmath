import BEDC.Derived.MetricCompletionFiniteUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletionFiniteClassifierExactness [AskSetup] [PackageSetup]
    {M B W E R S H C P N M' B' W' E' R' S' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFiniteCarrier M B W E R S H C P N bundle pkg →
      hsame M M' →
        hsame B B' →
          hsame W W' →
            hsame E E' →
              hsame R R' →
                hsame S S' →
                  hsame H H' →
                    hsame C C' →
                      hsame P P' →
                        hsame N N' →
                          PkgSig bundle P' pkg →
                            PkgSig bundle N' pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row N' ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M' ∨ hsame row B' ∨ hsame row W' ∨
                                      hsame row E' ∨ hsame row R' ∨ hsame row S' ∨
                                        hsame row N')
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P' pkg ∧
                                      PkgSig bundle N' pkg)
                                  hsame ∧
                                MetricCompletionFiniteCarrier M' B' W' E' R' S' H' C'
                                  P' N' bundle pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier sameM sameB sameW sameE sameR sameS sameH sameC sameP sameN
    provenancePkg localNamePkg
  obtain ⟨metricUnary, basisUnary, windowUnary, embeddingUnary, readbackUnary,
    selectorUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _oldProvenancePkg, _oldLocalNamePkg⟩ := carrier
  have metricUnary' : UnaryHistory M' := unary_transport metricUnary sameM
  have basisUnary' : UnaryHistory B' := unary_transport basisUnary sameB
  have windowUnary' : UnaryHistory W' := unary_transport windowUnary sameW
  have embeddingUnary' : UnaryHistory E' := unary_transport embeddingUnary sameE
  have readbackUnary' : UnaryHistory R' := unary_transport readbackUnary sameR
  have selectorUnary' : UnaryHistory S' := unary_transport selectorUnary sameS
  have transportUnary' : UnaryHistory H' := unary_transport transportUnary sameH
  have replayUnary' : UnaryHistory C' := unary_transport replayUnary sameC
  have provenanceUnary' : UnaryHistory P' := unary_transport provenanceUnary sameP
  have localNameUnary' : UnaryHistory N' := unary_transport localNameUnary sameN
  have primedCarrier :
      MetricCompletionFiniteCarrier M' B' W' E' R' S' H' C' P' N' bundle pkg := by
    exact
      ⟨metricUnary', basisUnary', windowUnary', embeddingUnary', readbackUnary',
        selectorUnary', transportUnary', replayUnary', provenanceUnary', localNameUnary',
        provenancePkg, localNamePkg⟩
  have certAndPkg :
      SemanticNameCert
          (fun row : BHist => hsame row N' ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M' ∨ hsame row B' ∨ hsame row W' ∨ hsame row E' ∨
              hsame row R' ∨ hsame row S' ∨ hsame row N')
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg)
          hsame ∧
        PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg :=
    MetricCompletionFiniteCarrier_namecert_obligations primedCarrier
  exact ⟨certAndPkg.left, primedCarrier⟩

end BEDC.Derived.MetricCompletionFiniteUp
