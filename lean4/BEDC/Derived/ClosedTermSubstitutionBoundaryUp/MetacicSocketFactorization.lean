import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.BoundaryRoutes

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryMetacicSocketFactorization [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer metacicConsumer
      socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont shift substitution ledger →
        Cont substitution depth audit →
          Cont ledger audit route →
            Cont route audit consumer →
              Cont consumer route metacicConsumer →
                Cont metacicConsumer ledger socketRead →
                  PkgSig bundle consumer pkg →
                    PkgSig bundle metacicConsumer pkg →
                      PkgSig bundle socketRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              ClosedTermSubstitutionBoundaryClassifier source value depth shift
                                  substitution ∧
                                hsame row socketRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row value ∨ hsame row depth ∨
                                hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                                  hsame row consumer ∨ hsame row metacicConsumer ∨
                                    hsame row socketRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont consumer route metacicConsumer ∧
                                Cont metacicConsumer ledger socketRead ∧
                                  PkgSig bundle socketRead pkg)
                            hsame ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteMetacic metacicLedgerSocket consumerPkg metacicPkg
    socketPkg
  have metacicPacket :=
    ClosedTermSubstitutionBoundaryMetacicConsumerNonescape classifier shiftSubstitutionLedger
      substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerRouteMetacic
      consumerPkg metacicPkg
  obtain ⟨_sourceUnary, _valueUnary, _depthUnary, _shiftUnary, _substitutionUnary,
    ledgerUnary, _auditUnary, _routeUnary, _consumerUnary, metacicUnary,
    _consumerRouteMetacic, _consumerPkg, _metacicPkg, _consumerCert⟩ := metacicPacket
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed metacicUnary ledgerUnary metacicLedgerSocket
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
              hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row route ∨ hsame row consumer ∨
                hsame row metacicConsumer ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont consumer route metacicConsumer ∧
              Cont metacicConsumer ledger socketRead ∧ PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro socketRead ⟨classifier, hsame_refl socketRead, socketUnary⟩
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
          ⟨source.left,
            hsame_trans (hsame_symm sameRows) source.right.left,
            unary_transport source.right.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.right.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.right, consumerRouteMetacic, metacicLedgerSocket, socketPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
