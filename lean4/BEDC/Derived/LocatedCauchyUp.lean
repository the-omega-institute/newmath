import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCauchyCarrier [AskSetup] [PackageSetup]
    (schedule endpoints modulus witnesses transport routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory endpoints ∧ UnaryHistory modulus ∧
    UnaryHistory witnesses ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont schedule endpoints modulus ∧
        Cont modulus witnesses transport ∧ Cont transport routes provenance ∧
          Cont provenance nameRow routes ∧ PkgSig bundle provenance pkg

theorem LocatedCauchyCarrier_window_stability [AskSetup] [PackageSetup]
    {schedule endpoints modulus witnesses transport routes provenance nameRow schedule' endpoints'
      modulus' witnesses' transport' routes' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyCarrier schedule endpoints modulus witnesses transport routes provenance nameRow
        bundle pkg ->
      hsame schedule schedule' ->
        hsame endpoints endpoints' ->
          hsame witnesses witnesses' ->
            hsame routes routes' ->
              hsame provenance provenance' ->
                hsame nameRow nameRow' ->
                  Cont schedule' endpoints' modulus' ->
                    Cont modulus' witnesses' transport' ->
                      Cont transport' routes' provenance' ->
                        Cont provenance' nameRow' routes' ->
                          LocatedCauchyCarrier schedule' endpoints' modulus' witnesses'
                              transport' routes' provenance' nameRow' bundle pkg ∧
                            hsame modulus modulus' ∧ hsame transport transport' := by
  intro carrier sameSchedule sameEndpoints sameWitnesses sameRoutes sameProvenance sameNameRow
    scheduleEndpointsModulus' modulusWitnessesTransport' transportRoutesProvenance'
    provenanceNameRoutes'
  rcases carrier with
    ⟨scheduleUnary, endpointsUnary, modulusUnary, witnessesUnary, transportUnary, routesUnary,
      provenanceUnary, nameUnary, scheduleEndpointsModulus, modulusWitnessesTransport,
      transportRoutesProvenance, provenanceNameRoutes, pkgSig⟩
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame sameSchedule sameEndpoints scheduleEndpointsModulus
      scheduleEndpointsModulus'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameModulus sameWitnesses modulusWitnessesTransport
      modulusWitnessesTransport'
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have endpointsUnary' : UnaryHistory endpoints' :=
    unary_transport endpointsUnary sameEndpoints
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have witnessesUnary' : UnaryHistory witnesses' :=
    unary_transport witnessesUnary sameWitnesses
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory nameRow' :=
    unary_transport nameUnary sameNameRow
  cases sameProvenance
  exact And.intro
    (And.intro scheduleUnary'
      (And.intro endpointsUnary'
        (And.intro modulusUnary'
          (And.intro witnessesUnary'
            (And.intro transportUnary'
              (And.intro routesUnary'
                (And.intro provenanceUnary'
                  (And.intro nameUnary'
                    (And.intro scheduleEndpointsModulus'
                      (And.intro modulusWitnessesTransport'
                        (And.intro transportRoutesProvenance'
                          (And.intro provenanceNameRoutes' pkgSig))))))))))))
    (And.intro sameModulus sameTransport)

theorem LocatedCauchyCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {schedule endpoints modulus witnesses transport routes provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyCarrier schedule endpoints modulus witnesses transport routes provenance nameRow
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          hsame ∧
        UnaryHistory schedule ∧ UnaryHistory endpoints ∧ UnaryHistory modulus ∧
          UnaryHistory witnesses ∧ Cont schedule endpoints modulus ∧
            Cont modulus witnesses transport ∧ Cont transport routes provenance ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  rcases carrier with
    ⟨scheduleUnary, endpointsUnary, modulusUnary, witnessesUnary, _transportUnary, _routesUnary,
      _provenanceUnary, _nameUnary, scheduleEndpointsModulus, modulusWitnessesTransport,
      transportRoutesProvenance, _provenanceNameRoutes, pkgSig⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, scheduleUnary, endpointsUnary, modulusUnary, witnessesUnary,
      scheduleEndpointsModulus, modulusWitnessesTransport, transportRoutesProvenance, pkgSig⟩

theorem LocatedCauchyCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {schedule endpoints modulus witnesses transport routes provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyCarrier schedule endpoints modulus witnesses transport routes provenance nameRow
        bundle pkg ->
      Cont provenance (BHist.e0 nameRow) routes -> False := by
  intro carrier extendedNameRoute
  rcases carrier with
    ⟨_, _, _, _, _, _, _, _, _, _, _, provenanceNameRoute, _⟩
  have sameName : hsame nameRow (BHist.e0 nameRow) :=
    cont_left_cancel provenanceNameRoute extendedNameRoute
  exact hsame_extension_self_absurd.left nameRow (hsame_symm sameName)

end BEDC.Derived.LocatedCauchyUp
