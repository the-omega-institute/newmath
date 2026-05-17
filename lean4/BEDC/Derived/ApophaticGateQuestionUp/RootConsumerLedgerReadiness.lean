import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_consumer_ledger_readiness [AskSetup]
    [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead auditRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont route provenance rootRead →
        Cont readback route auditRead →
          Cont rootRead auditRead consumerRead →
            PkgSig bundle rootRead pkg →
              PkgSig bundle auditRead pkg →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        ApophaticGateQuestionCarrier socket question refusal readback transport
                          route provenance nameRow bundle pkg ∧ hsame row consumerRead)
                      (fun row : BHist =>
                        hsame row consumerRead ∧ UnaryHistory row ∧
                          Cont rootRead auditRead consumerRead)
                      (fun row : BHist =>
                        PkgSig bundle rootRead pkg ∧ PkgSig bundle auditRead pkg ∧
                          PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
                      hsame ∧
                    UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier rootRoute auditRoute consumerRoute rootPkg auditPkg consumerPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, _provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rootUnary auditUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ UnaryHistory row ∧
              Cont rootRead auditRead consumerRead)
          (fun row : BHist =>
            PkgSig bundle rootRead pkg ∧ PkgSig bundle auditRead pkg ∧
              PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨carrierPacket, hsame_refl consumerRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport consumerUnary (hsame_symm source.right),
            consumerRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨rootPkg, auditPkg, consumerPkg, source.right⟩
    }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.ApophaticGateQuestionUp
