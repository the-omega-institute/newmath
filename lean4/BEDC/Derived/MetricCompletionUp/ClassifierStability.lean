import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.ClassifierStability

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_classifier_stability [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert source' filterBranch' netBranch' readback' separated' transport' replay'
      provenance' localCert' classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      MetricCompletionCarrier source' filterBranch' netBranch' readback' separated' transport'
        replay' provenance' localCert' bundle pkg →
        hsame source source' →
          hsame filterBranch filterBranch' →
            hsame netBranch netBranch' →
              hsame readback readback' →
                hsame separated separated' →
                  hsame replay replay' →
                    Cont provenance' localCert' classifierRead →
                      PkgSig bundle classifierRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source' ∨ hsame row filterBranch' ∨
                                hsame row netBranch' ∨ hsame row readback' ∨
                                  hsame row separated' ∨ hsame row classifierRead)
                            (fun row : BHist =>
                              hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
                            hsame ∧
                          UnaryHistory classifierRead ∧ hsame source source' ∧
                            hsame filterBranch filterBranch' ∧ hsame netBranch netBranch' ∧
                              hsame readback readback' ∧ hsame separated separated' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro _carrier carrier' sourceSame filterSame netSame readbackSame separatedSame _replaySame
    classifierRoute classifierPkg
  obtain ⟨_sourceUnary', _filterUnary', _netUnary', _readbackUnary', _separatedUnary',
    _transportUnary', _replayUnary', provenanceUnary', localCertUnary', _replayRoute',
    _transportSame', _provenancePkg', _localCertPkg'⟩ := carrier'
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed provenanceUnary' localCertUnary' classifierRoute
  have sourceClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source' ∨ hsame row filterBranch' ∨ hsame row netBranch' ∨
              hsame row readback' ∨ hsame row separated' ∨ hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro classifierRead sourceClassifier
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, classifierPkg⟩
    }
  exact
    ⟨cert, classifierUnary, sourceSame, filterSame, netSame, readbackSame, separatedSame⟩

end BEDC.Derived.MetricCompletionUp.ClassifierStability
