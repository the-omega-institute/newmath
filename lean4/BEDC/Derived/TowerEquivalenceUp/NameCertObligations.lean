import BEDC.Derived.TowerEquivalenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TowerEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TowerEquivalence_namecert_obligations [AskSetup] [PackageSetup]
    {tower tower' approx approx' physical physical' openFit openFit' objectivity ledger descent
      endpoint transport provenance name endpointRead ledgerRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory tower ->
      UnaryHistory tower' ->
        UnaryHistory ledger ->
          UnaryHistory descent ->
            UnaryHistory endpoint ->
              UnaryHistory transport ->
                Cont tower tower' endpointRead ->
                  Cont ledger descent ledgerRead ->
                    Cont endpoint transport descentRead ->
                      PkgSig bundle descentRead pkg ->
                        towerEquivalenceFields
                            (TowerEquivalenceUp.mk tower tower' approx approx' physical
                              physical' openFit openFit' objectivity ledger descent endpoint
                              transport provenance name) =
                          [tower, tower', approx, approx', physical, physical', openFit,
                            openFit', objectivity, ledger, descent, endpoint, transport,
                            provenance, name] ∧
                          UnaryHistory endpointRead ∧
                            UnaryHistory ledgerRead ∧
                              UnaryHistory descentRead ∧
                                Cont tower tower' endpointRead ∧
                                  Cont ledger descent ledgerRead ∧
                                    Cont endpoint transport descentRead ∧
                                      PkgSig bundle descentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro towerUnary towerUnary' ledgerUnary descentUnary endpointUnary transportUnary
    endpointRoute ledgerRoute descentRoute descentPkg
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed towerUnary towerUnary' endpointRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary descentUnary ledgerRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed endpointUnary transportUnary descentRoute
  exact
    ⟨rfl, endpointReadUnary, ledgerReadUnary, descentReadUnary, endpointRoute, ledgerRoute,
      descentRoute, descentPkg⟩

theorem TowerEquivalence_ledger_descent_stability
    {tower tower' approx approx' physical physical' openFit openFit' objectivity ledger descent
      endpoint transport provenance name ledger' descent' route route' : BHist} :
    UnaryHistory ledger' ->
      UnaryHistory descent' ->
        hsame ledger ledger' ->
          hsame descent descent' ->
            Cont ledger descent route ->
              Cont ledger' descent' route' ->
                towerEquivalenceFields
                    (TowerEquivalenceUp.mk tower tower' approx approx' physical physical'
                      openFit openFit' objectivity ledger descent endpoint transport
                      provenance name) =
                  [tower, tower', approx, approx', physical, physical', openFit, openFit',
                    objectivity, ledger, descent, endpoint, transport, provenance, name] ∧
                  towerEquivalenceFields
                      (TowerEquivalenceUp.mk tower tower' approx approx' physical physical'
                        openFit openFit' objectivity ledger' descent' endpoint transport
                        provenance name) =
                    [tower, tower', approx, approx', physical, physical', openFit, openFit',
                      objectivity, ledger', descent', endpoint, transport, provenance, name] ∧
                    UnaryHistory route' ∧ hsame route route' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro ledgerUnary' descentUnary' sameLedger sameDescent ledgerRoute ledgerRoute'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed ledgerUnary' descentUnary' ledgerRoute'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameLedger sameDescent ledgerRoute ledgerRoute'
  exact ⟨rfl, rfl, routeUnary', sameRoute⟩

theorem TowerEquivalenceCarrier_endpoint_refusal
    {R L D B H endpoint ledgerRoute descentRoute transportRoute : BHist} :
    UnaryHistory R ->
      UnaryHistory L ->
        UnaryHistory D ->
          UnaryHistory B ->
            UnaryHistory H ->
              Cont R L endpoint ->
                Cont endpoint D ledgerRoute ->
                  Cont ledgerRoute B descentRoute ->
                    Cont descentRoute H transportRoute ->
                      UnaryHistory endpoint ∧ UnaryHistory ledgerRoute ∧
                        UnaryHistory descentRoute ∧ UnaryHistory transportRoute ∧
                          Cont R L endpoint ∧ Cont endpoint D ledgerRoute ∧
                            Cont ledgerRoute B descentRoute ∧
                              Cont descentRoute H transportRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryR unaryL unaryD unaryB unaryH endpointRoute ledgerRouteRow descentRouteRow
    transportRouteRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed unaryR unaryL endpointRoute
  have ledgerRouteUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed endpointUnary unaryD ledgerRouteRow
  have descentRouteUnary : UnaryHistory descentRoute :=
    unary_cont_closed ledgerRouteUnary unaryB descentRouteRow
  have transportRouteUnary : UnaryHistory transportRoute :=
    unary_cont_closed descentRouteUnary unaryH transportRouteRow
  exact
    ⟨endpointUnary, ledgerRouteUnary, descentRouteUnary, transportRouteUnary, endpointRoute,
      ledgerRouteRow, descentRouteRow, transportRouteRow⟩

end BEDC.Derived.TowerEquivalenceUp
