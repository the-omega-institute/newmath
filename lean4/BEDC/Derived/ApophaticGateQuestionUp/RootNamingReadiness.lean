import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_naming_readiness [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead auditRead
      refusalRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont route provenance rootRead →
        Cont readback route auditRead →
          Cont refusal readback refusalRead →
            Cont refusal auditRead handoff →
              PkgSig bundle rootRead pkg →
                PkgSig bundle auditRead pkg →
                  PkgSig bundle refusalRead pkg →
                    PkgSig bundle handoff pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            ApophaticGateQuestionCarrier socket question refusal readback
                              transport route provenance nameRow bundle pkg ∧ hsame row nameRow)
                          (fun row : BHist =>
                            hsame row nameRow ∧ UnaryHistory row ∧
                              Cont readback route nameRow)
                          (fun row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                              PkgSig bundle auditRead pkg ∧
                                PkgSig bundle refusalRead pkg ∧
                                  PkgSig bundle handoff pkg ∧ hsame row nameRow)
                          hsame ∧
                        UnaryHistory socket ∧ UnaryHistory question ∧
                          UnaryHistory refusal ∧ UnaryHistory readback ∧
                            UnaryHistory nameRow ∧ UnaryHistory rootRead ∧
                              UnaryHistory auditRead ∧ UnaryHistory refusalRead ∧
                                UnaryHistory handoff ∧ Cont socket question readback ∧
                                  Cont question refusal route ∧
                                    Cont readback route nameRow ∧
                                      Cont route provenance rootRead ∧
                                        Cont readback route auditRead ∧
                                          Cont refusal readback refusalRead ∧
                                            Cont refusal auditRead handoff := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier rootRoute auditRoute refusalRoute handoffRoute rootPkg auditPkg refusalPkg
    handoffPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    _refusalReadbackTransport, readbackRouteNameRow, _readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed refusalUnary auditUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist =>
            hsame row nameRow ∧ UnaryHistory row ∧ Cont readback route nameRow)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              PkgSig bundle auditRead pkg ∧ PkgSig bundle refusalRead pkg ∧
                PkgSig bundle handoff pkg ∧ hsame row nameRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
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
          ⟨source.right, unary_transport nameRowUnary (hsame_symm source.right),
            readbackRouteNameRow⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootPkg, auditPkg, refusalPkg, handoffPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, nameRowUnary,
      rootUnary, auditUnary, refusalReadUnary, handoffUnary, socketQuestionReadback,
      questionRefusalRoute, readbackRouteNameRow, rootRoute, auditRoute, refusalRoute,
      handoffRoute⟩

end BEDC.Derived.ApophaticGateQuestionUp
