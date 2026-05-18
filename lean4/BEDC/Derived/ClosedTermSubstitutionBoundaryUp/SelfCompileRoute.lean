import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryPacket_self_compile_route
    {source value depth shift substitution ledger audit selfCompileRead : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont shift substitution ledger →
        Cont substitution depth audit →
          Cont ledger audit selfCompileRead →
            UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory selfCompileRead ∧
              Cont source value shift ∧ Cont shift depth substitution ∧
                Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                  Cont ledger audit selfCompileRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have selfCompileUnary : UnaryHistory selfCompileRead :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  exact
    ⟨ledgerUnary, auditUnary, selfCompileUnary, sourceValueShift, shiftDepthSubstitution,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
