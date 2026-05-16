import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_supply_kind_route_totality [AskSetup] [PackageSetup]
    {socket question refusal readback readback' transport route provenance nameRow auditRead
      supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question readback' →
        Cont readback' route auditRead →
          Cont question refusal supplyRead →
            PkgSig bundle auditRead pkg →
              PkgSig bundle supplyRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row refusal ∧
                        ApophaticGateQuestionCarrier socket question refusal readback transport
                          route provenance nameRow bundle pkg)
                    (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont socket question readback' ∧ Cont question refusal supplyRead ∧
                        Cont readback' route auditRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle auditRead pkg ∧ PkgSig bundle supplyRead pkg)
                    hsame ∧
                  UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                    UnaryHistory readback' ∧ UnaryHistory supplyRead ∧
                      UnaryHistory auditRead ∧ Cont socket question readback' ∧
                        Cont question refusal supplyRead ∧ Cont readback' route auditRead ∧
                          hsame readback' (append socket question) ∧
                            PkgSig bundle supplyRead pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketQuestionReadback auditRoute questionRefusalSupply auditPkg supplyPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, _readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback' :=
    unary_cont_closed socketUnary questionUnary socketQuestionReadback
  have supplyUnary : UnaryHistory supplyRead :=
    unary_cont_closed questionUnary refusalUnary questionRefusalSupply
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have readbackSameSourceQuestion : hsame readback' (append socket question) := by
    exact socketQuestionReadback
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusal ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket question readback' ∧ Cont question refusal supplyRead ∧
              Cont readback' route auditRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle auditRead pkg ∧ PkgSig bundle supplyRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro refusal ⟨hsame_refl refusal, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro _row source
      exact ⟨source.left, unary_transport refusalUnary (hsame_symm source.left)⟩
    · intro _row _source
      exact
        ⟨socketQuestionReadback, questionRefusalSupply, auditRoute, provenancePkg,
          auditPkg, supplyPkg⟩
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, supplyUnary,
      auditUnary, socketQuestionReadback, questionRefusalSupply, auditRoute,
      readbackSameSourceQuestion, supplyPkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
