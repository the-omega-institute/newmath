import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_refusal_row_transport [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow socket' question'
      refusal' readback' transport' route' provenance' nameRow' auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance nameRow bundle pkg ->
      hsame socket socket' -> hsame question question' -> hsame refusal refusal' ->
        hsame readback readback' -> hsame transport transport' -> hsame route route' ->
          hsame provenance provenance' -> hsame nameRow nameRow' ->
            PkgSig bundle provenance' pkg -> Cont readback' route' auditRead ->
              PkgSig bundle auditRead pkg ->
                SemanticNameCert
                  (fun row : BHist => ApophaticGateQuestionCarrier socket' question'
                    refusal' readback' transport' route' provenance' nameRow' bundle pkg ∧
                      hsame row refusal')
                  (fun row : BHist => hsame row refusal' ∧ UnaryHistory row)
                  (fun row : BHist => PkgSig bundle provenance' pkg ∧ hsame row refusal' ∧
                    Cont question' refusal' route')
                  hsame ∧
                UnaryHistory refusal' ∧ UnaryHistory auditRead ∧ Cont question' refusal' route' ∧
                  Cont readback' route' auditRead ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameSocket sameQuestion sameRefusal sameReadback sameTransport sameRoute
    sameProvenance sameNameRow provenancePkg' readbackRouteAudit auditPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    refusalReadbackTransport, readbackRouteNameRow, readbackSameSocketQuestion,
    _provenancePkg⟩ := carrier
  cases sameSocket
  cases sameQuestion
  cases sameRefusal
  cases sameReadback
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
      refusalReadbackTransport, readbackRouteNameRow, readbackSameSocketQuestion,
      provenancePkg'⟩
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticGateQuestionCarrier socket question refusal readback transport route
            provenance nameRow bundle pkg ∧ hsame row refusal)
        (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ hsame row refusal ∧ Cont question refusal route)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refusal ⟨carrierPacket, hsame_refl refusal⟩
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
        exact ⟨source.right, unary_transport refusalUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg', source.right, questionRefusalRoute⟩
    }
  exact ⟨cert, refusalUnary, auditUnary, questionRefusalRoute, readbackRouteAudit, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
