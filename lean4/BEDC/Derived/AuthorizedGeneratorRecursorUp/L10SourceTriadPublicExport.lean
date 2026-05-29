import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10SourceTriadPublicExport [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N sourceRead dyadicRead streamRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O N sourceRead →
        Cont sourceRead D dyadicRead →
          Cont dyadicRead C streamRead →
            Cont dyadicRead C streamRead →
              Cont streamRead G regseqRead →
                Cont regseqRead N realRead →
                  PkgSig bundle realRead pkg →
                    UnaryHistory sourceRead ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                        UnaryHistory realRead ∧ Cont O N sourceRead ∧
                          Cont sourceRead D dyadicRead ∧
                            Cont dyadicRead C streamRead ∧ Cont streamRead G regseqRead ∧
                              Cont regseqRead N realRead ∧ hsame H (append A C) ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputNameSource sourceDescentDyadic dyadicContinuationStream
    _dyadicContinuationStreamAgain streamBoundaryRegseq regseqNameReal realPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, _auditUnary, transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, localNameUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed outputUnary localNameUnary outputNameSource
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sourceUnary descentUnary sourceDescentDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary continuationUnary dyadicContinuationStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary boundaryUnary streamBoundaryRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary localNameUnary regseqNameReal
  exact
    ⟨sourceUnary, dyadicUnary, streamUnary, regseqUnary, realUnary, outputNameSource,
      sourceDescentDyadic, dyadicContinuationStream, streamBoundaryRegseq, regseqNameReal,
      transportAuditContinuation, provenancePkg, realPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
