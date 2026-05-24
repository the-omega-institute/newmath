import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitSubsequenceTailStability [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name subsequenceWindow subsequenceRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      UnaryHistory subsequenceWindow ->
      Cont windowSchedule subsequenceWindow subsequenceRead ->
        Cont subsequenceRead dyadicLedger tailRead ->
          PkgSig bundle tailRead pkg ->
            UnaryHistory windowSchedule ∧ UnaryHistory subsequenceWindow ∧
              UnaryHistory subsequenceRead ∧ UnaryHistory tailRead ∧
                Cont windowSchedule subsequenceWindow subsequenceRead ∧
                  Cont subsequenceRead dyadicLedger tailRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier subsequenceWindowUnary subsequenceCont tailCont tailPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, _classifierUnary,
      _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _routeCont,
      _classifierCont, _transportSame, _routeSame, provenancePkg, _namePkg⟩
  have subsequenceReadUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed windowUnary subsequenceWindowUnary subsequenceCont
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed subsequenceReadUnary dyadicUnary tailCont
  exact
    ⟨windowUnary, subsequenceWindowUnary, subsequenceReadUnary, tailReadUnary,
      subsequenceCont, tailCont, provenancePkg, tailPkg⟩

end BEDC.Derived.RealSequenceLimitUp
