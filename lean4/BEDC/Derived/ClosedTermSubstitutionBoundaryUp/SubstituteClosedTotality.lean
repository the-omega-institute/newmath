import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySubstituteClosedTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution substitutionRead ledger audit consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift depth substitutionRead ->
        Cont substitutionRead value ledger ->
          Cont ledger depth audit ->
            Cont audit depth consumer ->
              PkgSig bundle consumer pkg ->
                hsame substitutionRead substitution /\ UnaryHistory substitutionRead /\
                  UnaryHistory ledger /\ UnaryHistory audit /\ UnaryHistory consumer /\
                    Cont substitutionRead value ledger /\ Cont ledger depth audit /\
                      Cont audit depth consumer /\ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier shiftDepthSubstitutionRead substitutionReadValueLedger ledgerDepthAudit
    auditDepthConsumer consumerPkg
  have rows :=
    ClosedTermSubstitutionBoundarySubstitutionRowExactness classifier
      shiftDepthSubstitutionRead substitutionReadValueLedger ledgerDepthAudit
  obtain ⟨sameSubstitutionRead, substitutionReadUnary, ledgerUnary, auditUnary,
    substitutionReadValueLedger', ledgerDepthAudit'⟩ := rows
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, _shiftUnary, _substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed auditUnary depthUnary auditDepthConsumer
  exact
    ⟨sameSubstitutionRead, substitutionReadUnary, ledgerUnary, auditUnary, consumerUnary,
      substitutionReadValueLedger', ledgerDepthAudit', auditDepthConsumer, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
