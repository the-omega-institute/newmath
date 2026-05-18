import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryBinderSealFactorization [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit binderRead binderSeal nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit binderRead ->
            Cont binderRead substitution binderSeal ->
              Cont binderSeal audit nameRead ->
                PkgSig bundle nameRead pkg ->
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory binderRead ∧
                    UnaryHistory binderSeal ∧ UnaryHistory nameRead ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit binderRead ∧
                          Cont binderRead substitution binderSeal ∧
                            Cont binderSeal audit nameRead ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditBinderRead
    binderReadSubstitutionBinderSeal binderSealAuditNameRead nameReadPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have binderReadUnary : UnaryHistory binderRead :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditBinderRead
  have binderSealUnary : UnaryHistory binderSeal :=
    unary_cont_closed binderReadUnary substitutionUnary binderReadSubstitutionBinderSeal
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed binderSealUnary auditUnary binderSealAuditNameRead
  exact
    ⟨ledgerUnary, auditUnary, binderReadUnary, binderSealUnary, nameReadUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditBinderRead,
      binderReadSubstitutionBinderSeal, binderSealAuditNameRead, nameReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
