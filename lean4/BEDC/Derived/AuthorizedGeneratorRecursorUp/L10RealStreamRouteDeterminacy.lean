import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10RealStreamHandoffRow
import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10RealStreamOutputFactorization

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRealStreamRouteDeterminacy [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamRead regSeqRead realRead handoff normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A streamRead ->
        Cont streamRead C regSeqRead ->
          Cont regSeqRead G realRead ->
            Cont realRead N handoff ->
              Cont C O normalRead ->
                PkgSig bundle handoff pkg ->
                  PkgSig bundle normalRead pkg ->
                    UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                      UnaryHistory realRead ∧ UnaryHistory handoff ∧ UnaryHistory normalRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle handoff pkg ∧ PkgSig bundle normalRead pkg := by
  -- BEDC touchpoint anchor: AuthorizedGeneratorRecursorCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal realNameHandoff
    continuationOutputNormal handoffPkg normalPkg
  have streamRows :=
    AuthorizedGeneratorRecursorRealStreamHandoffRow carrier outputAuditStream
      streamContinuationRegSeq regSeqBoundaryReal realNameHandoff handoffPkg
  have normalRows :=
    AuthorizedGeneratorRecursorL10RealStreamOutputFactorization carrier continuationOutputNormal
      normalPkg
  rcases streamRows with
    ⟨_outputUnary, _auditUnary, _continuationUnary, _boundaryUnary, _nameUnary, streamUnary,
      regSeqUnary, realUnary, handoffUnary, sameAuditContinuation, _outputAuditStream,
      _streamContinuationRegSeq, _regSeqBoundaryReal, _realNameHandoff, provenancePkg,
      handoffPkg'⟩
  rcases normalRows with
    ⟨_continuationUnary', _outputUnary', normalUnary, _continuationOutputNormal,
      _sameAuditContinuation', _provenancePkg', normalPkg'⟩
  exact
    ⟨streamUnary, regSeqUnary, realUnary, handoffUnary, normalUnary, sameAuditContinuation,
      provenancePkg, handoffPkg', normalPkg'⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
