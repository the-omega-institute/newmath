import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_auditgate_composition_boundary_lock
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead auditRead
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        Cont refusal auditRead handoff →
          Cont route provenance rootRead →
            PkgSig bundle auditRead pkg →
              PkgSig bundle handoff pkg →
                PkgSig bundle rootRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row handoff ∧
                          ApophaticGateQuestionCarrier socket question refusal readback
                            transport route provenance nameRow bundle pkg)
                      (fun row : BHist =>
                        hsame row handoff ∧ UnaryHistory row ∧
                          Cont refusal auditRead handoff)
                      (fun row : BHist =>
                        Cont socket question readback ∧ Cont question refusal route ∧
                          Cont readback route auditRead ∧ Cont refusal auditRead handoff ∧
                            Cont route provenance rootRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle auditRead pkg ∧
                                  PkgSig bundle handoff pkg ∧
                                    PkgSig bundle rootRead pkg ∧ hsame row handoff)
                      hsame ∧
                    UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                      UnaryHistory auditRead ∧ UnaryHistory handoff ∧
                        UnaryHistory rootRead ∧ Cont socket question readback ∧
                          Cont question refusal route ∧ Cont readback route auditRead ∧
                            Cont refusal auditRead handoff ∧
                              Cont route provenance rootRead := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier auditRoute handoffRoute rootRoute auditPkg handoffPkg rootPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed refusalUnary auditUnary handoffRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row handoff ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row handoff ∧ UnaryHistory row ∧ Cont refusal auditRead handoff)
          (fun row : BHist =>
            Cont socket question readback ∧ Cont question refusal route ∧
              Cont readback route auditRead ∧ Cont refusal auditRead handoff ∧
                Cont route provenance rootRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle auditRead pkg ∧ PkgSig bundle handoff pkg ∧
                    PkgSig bundle rootRead pkg ∧ hsame row handoff)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoff ⟨hsame_refl handoff, carrierPacket⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, unary_transport handoffUnary (hsame_symm source.left),
            handoffRoute⟩
      ledger_sound := by
        intro _row source
        exact
          ⟨socketQuestionReadback, questionRefusalRoute, auditRoute, handoffRoute,
            rootRoute, provenancePkg, auditPkg, handoffPkg, rootPkg, source.left⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, auditUnary, handoffUnary, rootUnary,
      socketQuestionReadback, questionRefusalRoute, auditRoute, handoffRoute, rootRoute⟩

end BEDC.Derived.ApophaticGateQuestionUp
