import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApophaticGateQuestionCarrier [AskSetup] [PackageSetup]
    (socket question refusal readback transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
    UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont socket question readback ∧
        Cont question refusal route ∧ Cont refusal readback transport ∧
          Cont readback route nameRow ∧ hsame readback (append socket question) ∧
            PkgSig bundle provenance pkg

theorem ApophaticGateQuestionCarrier_source_before_question_route
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory readback ∧
          Cont socket question readback ∧ hsame readback (append socket question) ∧
            UnaryHistory auditRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier auditRoute
  obtain ⟨socketUnary, questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  exact
    ⟨socketUnary, questionUnary, readbackUnary, socketQuestionReadback,
      readbackSameSourceQuestion, auditUnary, provenancePkg⟩

theorem ApophaticGateQuestionCarrier_refusal_audit_ledger
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
          UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont question refusal route ∧
            Cont refusal readback transport ∧ Cont readback route nameRow ∧
              UnaryHistory auditRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier auditRoute
  obtain ⟨_socketUnary, _questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketQuestionReadback,
    questionRefusalRoute, refusalReadbackTransport, readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  exact
    ⟨refusalUnary, transportUnary, routeUnary, provenanceUnary, nameRowUnary,
      questionRefusalRoute, refusalReadbackTransport, readbackRouteNameRow, auditUnary,
      provenancePkg⟩

theorem ApophaticGateQuestionCarrier_audit_consumer_nonescape
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory readback ∧ UnaryHistory auditRead ∧
              Cont socket question readback ∧ Cont question refusal route ∧
                Cont readback route auditRead ∧ hsame readback (append socket question) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier auditRoute auditPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, auditUnary,
      socketQuestionReadback, questionRefusalRoute, auditRoute, readbackSameSourceQuestion,
      provenancePkg, auditPkg⟩

theorem ApophaticGateQuestionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameRow)
          hsame ∧
        UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
          UnaryHistory readback ∧ Cont socket question readback ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
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
        exact ⟨source.right, unary_transport nameRowUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary,
      socketQuestionReadback, provenancePkg⟩

theorem ApophaticGateQuestionCarrier_refusal_transport_scope [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow socket' question'
      refusal' readback' transport' route' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      hsame socket socket' →
        hsame question question' →
          hsame refusal refusal' →
            hsame readback readback' →
              hsame transport transport' →
                hsame route route' →
                  hsame provenance provenance' →
                    hsame nameRow nameRow' →
                      PkgSig bundle provenance' pkg →
                        ApophaticGateQuestionCarrier socket' question' refusal' readback'
                            transport' route' provenance' nameRow' bundle pkg ∧
                          hsame readback' (append socket' question') ∧
                            Cont question' refusal' route' ∧
                              Cont refusal' readback' transport' ∧
                                Cont readback' route' nameRow' ∧
                                  PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameSocket sameQuestion sameRefusal sameReadback sameTransport sameRoute
    sameProvenance sameNameRow provenancePkg'
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    refusalReadbackTransport, readbackRouteNameRow, readbackSameSourceQuestion,
    _provenancePkg⟩ := carrier
  cases sameSocket
  cases sameQuestion
  cases sameRefusal
  cases sameReadback
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  constructor
  · exact
      ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary, routeUnary,
        provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
        refusalReadbackTransport, readbackRouteNameRow, readbackSameSourceQuestion,
        provenancePkg'⟩
  · exact
      ⟨readbackSameSourceQuestion, questionRefusalRoute, refusalReadbackTransport,
        readbackRouteNameRow, provenancePkg'⟩

end BEDC.Derived.ApophaticGateQuestionUp
