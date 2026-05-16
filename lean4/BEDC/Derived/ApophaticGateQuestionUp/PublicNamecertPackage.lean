import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_public_namecert_package [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont route provenance rootRead →
        Cont readback route auditRead →
          PkgSig bundle rootRead pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticGateQuestionCarrier socket question refusal readback transport
                      route provenance nameRow bundle pkg ∧ hsame row nameRow)
                  (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                      PkgSig bundle auditRead pkg)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                  UnaryHistory readback ∧ UnaryHistory nameRow ∧ UnaryHistory rootRead ∧
                    UnaryHistory auditRead ∧ Cont socket question readback ∧
                      Cont question refusal route ∧ Cont readback route nameRow ∧
                        Cont route provenance rootRead ∧ Cont readback route auditRead ∧
                          hsame readback (append socket question) ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                              PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier rootRoute auditRoute rootPkg auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    _refusalReadbackTransport, readbackRouteNameRow, readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport nameRowUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨provenancePkg, rootPkg, auditPkg⟩
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, nameRowUnary, rootUnary,
      auditUnary, socketQuestionReadback, questionRefusalRoute, readbackRouteNameRow,
      rootRoute, auditRoute, readbackSameSourceQuestion, provenancePkg, rootPkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
