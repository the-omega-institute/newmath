import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10SourceTriadStrictObstruction [AskSetup]
    [PackageSetup]
    {I E M B D O A H C P G N sourceRead boundaryRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O N sourceRead ->
        Cont G N boundaryRead ->
          Cont sourceRead boundaryRead obstructionRead ->
            PkgSig bundle obstructionRead pkg ->
              UnaryHistory sourceRead ∧ UnaryHistory boundaryRead ∧
                UnaryHistory obstructionRead ∧ Cont O N sourceRead ∧
                  Cont G N boundaryRead ∧ Cont sourceRead boundaryRead obstructionRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputNameSource boundaryNameRead sourceBoundaryObstruction obstructionPkg
  obtain ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, outputUnary, _auditUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, boundaryUnary, localCertUnary,
    _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
    transportSame, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed outputUnary localCertUnary outputNameSource
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryNameRead
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed sourceUnary boundaryReadUnary sourceBoundaryObstruction
  exact
    ⟨sourceUnary, boundaryReadUnary, obstructionUnary, outputNameSource, boundaryNameRead,
      sourceBoundaryObstruction, transportSame, provenancePkg, obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
