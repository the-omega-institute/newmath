import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRegSeqRatRealCompletionLattice [AskSetup] [PackageSetup]
    {stream regSeq metricCompletion realSeal transport replay provenance localName streamRead
      regSeqRead completionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory regSeq ->
        UnaryHistory metricCompletion ->
          UnaryHistory realSeal ->
            UnaryHistory transport ->
              UnaryHistory replay ->
                UnaryHistory provenance ->
                  UnaryHistory localName ->
                    Cont stream regSeq streamRead ->
                      Cont streamRead metricCompletion regSeqRead ->
                        Cont regSeqRead realSeal completionRead ->
                          Cont completionRead localName sealRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row stream ∨ hsame row regSeq ∨
                                        hsame row metricCompletion ∨ hsame row realSeal ∨
                                          hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                                    UnaryHistory completionRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro streamUnary regSeqUnary metricCompletionUnary realSealUnary _transportUnary
    _replayUnary _provenanceUnary localNameUnary streamRegSeqRoute regSeqCompletionRoute
    completionRealRoute realNameRoute provenancePkg localNamePkg
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary regSeqUnary streamRegSeqRoute
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamReadUnary metricCompletionUnary regSeqCompletionRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed regSeqReadUnary realSealUnary completionRealRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed completionReadUnary localNameUnary realNameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regSeq ∨ hsame row metricCompletion ∨
              hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, streamReadUnary, regSeqReadUnary, completionReadUnary, sealReadUnary⟩

end BEDC.Derived.CauchyUp
