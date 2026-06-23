import BEDC.Derived.AxiomDependencyTupleUp.AuditConsumerCompleteness

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleConsumerReadiness [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName auditRead readyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont localName transport auditRead →
        Cont auditRead route readyRead →
          PkgSig bundle auditRead pkg →
            PkgSig bundle readyRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                      hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                        hsame row localName ∨ hsame row auditRead ∨ hsame row readyRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont mode witness route ∧
                      Cont route supply localName ∧ Cont localName transport auditRead ∧
                        Cont auditRead route readyRead ∧ PkgSig bundle readyRead pkg)
                  hsame ∧
                UnaryHistory auditRead ∧ UnaryHistory readyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier auditRoute readyRoute auditPkg readyPkg
  have auditResult :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ Cont mode witness route ∧
              Cont route supply localName ∧ Cont localName transport auditRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg)
          hsame ∧ UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
            UnaryHistory localName ∧ UnaryHistory auditRead :=
    AxiomDependencyTupleAuditConsumerCompleteness carrier auditRoute auditPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, _transportUnary, routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    _provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead := auditResult.right.right.right.right.right
  have readyUnary : UnaryHistory readyRead :=
    unary_cont_closed auditUnary routeUnary readyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row auditRead ∨ hsame row readyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont localName transport auditRead ∧ Cont auditRead route readyRead ∧
                PkgSig bundle readyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readyRead ⟨hsame_refl readyRead, readyUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, auditRoute, readyRoute,
          readyPkg⟩
  }
  exact ⟨cert, auditUnary, readyUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
