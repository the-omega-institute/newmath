import BEDC.Derived.MetacicConfluenceAuditWitnessUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetacicConfluenceAuditWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetacicConfluenceAuditWitnessCarrier [AskSetup] [PackageSetup]
    (parallel substitution diamond confluence obstruction component route ledger name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory parallel ∧
    UnaryHistory substitution ∧
      UnaryHistory diamond ∧
        UnaryHistory confluence ∧
          UnaryHistory obstruction ∧
            UnaryHistory component ∧
              UnaryHistory route ∧
                UnaryHistory ledger ∧
                  UnaryHistory name ∧
                    Cont parallel substitution route ∧
                      Cont route diamond ledger ∧
                        Cont obstruction component name ∧
                          PkgSig bundle name pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row name)
                              (fun row : BHist =>
                                hsame row parallel ∨ hsame row substitution ∨
                                  hsame row diamond ∨ hsame row confluence ∨
                                    hsame row name)
                              (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
                              hsame

theorem MetacicConfluenceAuditWitnessCarrier_conditional_boundary [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name
      substRead diamondRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence
      obstruction component route ledger name bundle pkg →
      Cont parallel substitution substRead →
        Cont substRead diamond diamondRead →
          Cont diamondRead confluence confluenceRead →
            PkgSig bundle confluenceRead pkg →
              UnaryHistory parallel ∧
                UnaryHistory substitution ∧
                  UnaryHistory diamond ∧
                    UnaryHistory confluence ∧
                      UnaryHistory substRead ∧
                        UnaryHistory diamondRead ∧
                          UnaryHistory confluenceRead ∧
                            Cont parallel substitution substRead ∧
                              Cont substRead diamond diamondRead ∧
                                Cont diamondRead confluence confluenceRead ∧
                                  PkgSig bundle confluenceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier substRoute diamondRoute confluenceRoute confluencePkg
  have parallelUnary : UnaryHistory parallel := carrier.left
  have substitutionUnary : UnaryHistory substitution := carrier.right.left
  have diamondUnary : UnaryHistory diamond := carrier.right.right.left
  have confluenceUnary : UnaryHistory confluence := carrier.right.right.right.left
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed parallelUnary substitutionUnary substRoute
  have diamondReadUnary : UnaryHistory diamondRead :=
    unary_cont_closed substReadUnary diamondUnary diamondRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed diamondReadUnary confluenceUnary confluenceRoute
  exact
    ⟨parallelUnary, substitutionUnary, diamondUnary, confluenceUnary, substReadUnary,
      diamondReadUnary, confluenceReadUnary, substRoute, diamondRoute, confluenceRoute,
      confluencePkg⟩

theorem MetacicConfluenceAuditWitnessNonescape [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name
      obstructionRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence
        obstruction component route ledger name bundle pkg →
      Cont obstruction component obstructionRead →
        Cont obstructionRead route boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory obstruction ∧
              UnaryHistory obstructionRead ∧
                UnaryHistory boundaryRead ∧
                  Cont obstruction component obstructionRead ∧
                    Cont obstructionRead route boundaryRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier obstructionRoute boundaryRoute boundaryPkg
  have obstructionUnary : UnaryHistory obstruction :=
    carrier.right.right.right.right.left
  have componentUnary : UnaryHistory component :=
    carrier.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    carrier.right.right.right.right.right.right.left
  have namePkg : PkgSig bundle name pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary componentUnary obstructionRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed obstructionReadUnary routeUnary boundaryRoute
  exact
    ⟨obstructionUnary, obstructionReadUnary, boundaryReadUnary, obstructionRoute,
      boundaryRoute, namePkg, boundaryPkg⟩

theorem MetacicConfluenceAuditWitness_sibling_lattice [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name routeRead
      obstructionRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      Cont parallel substitution routeRead →
        Cont obstruction component obstructionRead →
          Cont obstructionRead route boundaryRead →
            PkgSig bundle name pkg →
              PkgSig bundle boundaryRead pkg →
                UnaryHistory routeRead ∧
                  UnaryHistory obstructionRead ∧
                    UnaryHistory boundaryRead ∧
                      Cont parallel substitution routeRead ∧
                        Cont obstruction component obstructionRead ∧
                          Cont obstructionRead route boundaryRead ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier routeRoute obstructionRoute boundaryRoute namePkg boundaryPkg
  have parallelUnary : UnaryHistory parallel := carrier.left
  have substitutionUnary : UnaryHistory substitution := carrier.right.left
  have obstructionUnary : UnaryHistory obstruction :=
    carrier.right.right.right.right.left
  have componentUnary : UnaryHistory component :=
    carrier.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    carrier.right.right.right.right.right.right.left
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed parallelUnary substitutionUnary routeRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary componentUnary obstructionRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed obstructionReadUnary routeUnary boundaryRoute
  exact
    ⟨routeReadUnary, obstructionReadUnary, boundaryReadUnary, routeRoute, obstructionRoute,
      boundaryRoute, namePkg, boundaryPkg⟩

theorem MetacicConfluenceAuditWitness_finite_route_induction [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name final :
      BHist}
    {steps : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      (forall step : BHist, List.Mem step steps -> UnaryHistory step) →
        final = List.foldl append route steps →
          UnaryHistory final ∧ UnaryHistory obstruction ∧ Cont parallel substitution route ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier stepsUnary finalEq
  obtain ⟨_parallelUnary, _substitutionUnary, _diamondUnary, _confluenceUnary,
    obstructionUnary, _componentUnary, routeUnary, _ledgerUnary, _nameUnary,
    routeCont, _diamondCont, _obstructionCont, namePkg, _cert⟩ := carrier
  let rec foldUnaryClosed (current : BHist) :
      (rows : List BHist) →
        UnaryHistory current →
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) →
            UnaryHistory (List.foldl append current rows)
    | [], currentUnary, _ => currentUnary
    | head :: tail, currentUnary, rowsUnary =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append current head) :=
          unary_append_closed currentUnary headUnary
        have tailUnary : forall row : BHist, List.Mem row tail -> UnaryHistory row := by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem)
        foldUnaryClosed (append current head) tail nextUnary tailUnary
  have finalUnary : UnaryHistory final := by
    cases finalEq
    exact foldUnaryClosed route steps routeUnary stepsUnary
  exact ⟨finalUnary, obstructionUnary, routeCont, namePkg⟩

theorem MetacicConfluenceAuditWitness_obstruction_preservation [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name routeRead
      obstructionRead boundaryRead final : BHist}
    {steps : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      Cont parallel substitution routeRead →
        Cont obstruction component obstructionRead →
          Cont obstructionRead route boundaryRead →
            (forall step : BHist, List.Mem step steps -> UnaryHistory step) →
              final = List.foldl append boundaryRead steps →
                PkgSig bundle boundaryRead pkg →
                  UnaryHistory final ∧ UnaryHistory obstruction ∧ UnaryHistory boundaryRead ∧
                    Cont parallel substitution routeRead ∧
                      Cont obstruction component obstructionRead ∧
                        Cont obstructionRead route boundaryRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier routeRoute obstructionRoute boundaryRoute stepsUnary finalEq boundaryPkg
  obtain ⟨_parallelUnary, _substitutionUnary, _diamondUnary, _confluenceUnary,
    obstructionUnary, componentUnary, routeUnary, _ledgerUnary, _nameUnary,
    _carrierRoute, _ledgerRoute, _nameRoute, namePkg, _cert⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary componentUnary obstructionRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed obstructionReadUnary routeUnary boundaryRoute
  let rec foldUnaryClosed (current : BHist) :
      (rows : List BHist) →
        UnaryHistory current →
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) →
            UnaryHistory (List.foldl append current rows)
    | [], currentUnary, _ => currentUnary
    | head :: tail, currentUnary, rowsUnary =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append current head) :=
          unary_append_closed currentUnary headUnary
        have tailUnary : forall row : BHist, List.Mem row tail -> UnaryHistory row := by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem)
        foldUnaryClosed (append current head) tail nextUnary tailUnary
  have finalUnary : UnaryHistory final := by
    cases finalEq
    exact foldUnaryClosed boundaryRead steps boundaryReadUnary stepsUnary
  exact
    ⟨finalUnary, obstructionUnary, boundaryReadUnary, routeRoute, obstructionRoute,
      boundaryRoute, namePkg, boundaryPkg⟩

theorem MetacicConfluenceAuditWitness_obstruction_induction [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name final
      obstructionFinal : BHist}
    {steps obstructionSteps : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      (forall step : BHist, List.Mem step steps -> UnaryHistory step) →
        (forall step : BHist, List.Mem step obstructionSteps -> UnaryHistory step) →
          final = List.foldl append route steps →
            obstructionFinal = List.foldl append obstruction obstructionSteps →
              UnaryHistory final ∧ UnaryHistory obstructionFinal ∧
                Cont parallel substitution route ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier stepsUnary obstructionStepsUnary finalEq obstructionFinalEq
  obtain ⟨_parallelUnary, _substitutionUnary, _diamondUnary, _confluenceUnary,
    obstructionUnary, _componentUnary, routeUnary, _ledgerUnary, _nameUnary,
    routeCont, _diamondCont, _obstructionCont, namePkg, _cert⟩ := carrier
  let rec foldUnaryClosed (current : BHist) :
      (rows : List BHist) →
        UnaryHistory current →
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) →
            UnaryHistory (List.foldl append current rows)
    | [], currentUnary, _ => currentUnary
    | head :: tail, currentUnary, rowsUnary =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append current head) :=
          unary_append_closed currentUnary headUnary
        have tailUnary : forall row : BHist, List.Mem row tail -> UnaryHistory row := by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem)
        foldUnaryClosed (append current head) tail nextUnary tailUnary
  have finalUnary : UnaryHistory final := by
    cases finalEq
    exact foldUnaryClosed route steps routeUnary stepsUnary
  have obstructionFinalUnary : UnaryHistory obstructionFinal := by
    cases obstructionFinalEq
    exact foldUnaryClosed obstruction obstructionSteps obstructionUnary obstructionStepsUnary
  exact ⟨finalUnary, obstructionFinalUnary, routeCont, namePkg⟩

theorem MetacicConfluenceAuditWitness_local_diamond_boundary [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name routeRead
      obstructionRead boundaryRead diamondRead confluenceRead final : BHist}
    {steps : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      Cont parallel substitution routeRead →
        Cont routeRead diamond diamondRead →
          Cont diamondRead confluence confluenceRead →
            Cont obstruction component obstructionRead →
              Cont obstructionRead route boundaryRead →
                (forall step : BHist, List.Mem step steps -> UnaryHistory step) →
                  final = List.foldl append boundaryRead steps →
                    PkgSig bundle confluenceRead pkg →
                      PkgSig bundle boundaryRead pkg →
                        UnaryHistory confluenceRead ∧ UnaryHistory final ∧
                          UnaryHistory obstruction ∧ Cont routeRead diamond diamondRead ∧
                            Cont diamondRead confluence confluenceRead ∧
                              Cont obstructionRead route boundaryRead ∧
                                PkgSig bundle confluenceRead pkg ∧
                                  PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier routeRoute diamondRoute confluenceRoute obstructionRoute boundaryRoute
    stepsUnary finalEq confluencePkg boundaryPkg
  have conditional :=
    MetacicConfluenceAuditWitnessCarrier_conditional_boundary
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (substRead := routeRead)
      (diamondRead := diamondRead) (confluenceRead := confluenceRead)
      (bundle := bundle) (pkg := pkg) carrier routeRoute diamondRoute confluenceRoute
      confluencePkg
  obtain ⟨_parallelUnary, _substitutionUnary, _diamondUnary, _confluenceUnary,
    _routeReadUnary, _diamondReadUnary, confluenceReadUnary, _routeRoute,
    diamondRouteOut, confluenceRouteOut, confluencePkgOut⟩ := conditional
  have obstructionReplay :=
    MetacicConfluenceAuditWitness_obstruction_preservation
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (routeRead := routeRead)
      (obstructionRead := obstructionRead) (boundaryRead := boundaryRead) (final := final)
      (steps := steps) (bundle := bundle) (pkg := pkg) carrier routeRoute obstructionRoute
      boundaryRoute stepsUnary finalEq boundaryPkg
  obtain ⟨finalUnary, obstructionUnary, _boundaryReadUnary, _routeRouteOut,
    _obstructionRouteOut, boundaryRouteOut, _namePkg, boundaryPkgOut⟩ := obstructionReplay
  exact
    ⟨confluenceReadUnary, finalUnary, obstructionUnary, diamondRouteOut,
      confluenceRouteOut, boundaryRouteOut, confluencePkgOut, boundaryPkgOut⟩

theorem MetacicConfluenceAuditWitness_namecert_obligations [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name routeRead
      diamondRead confluenceRead obstructionRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      Cont parallel substitution routeRead →
        Cont routeRead diamond diamondRead →
          Cont diamondRead confluence confluenceRead →
            Cont obstruction component obstructionRead →
              Cont obstructionRead route boundaryRead →
                PkgSig bundle confluenceRead pkg →
                  PkgSig bundle boundaryRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row name)
                        (fun row : BHist =>
                          hsame row parallel ∨ hsame row substitution ∨ hsame row diamond ∨
                            hsame row confluence ∨ hsame row name)
                        (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
                        hsame ∧
                      UnaryHistory routeRead ∧
                        UnaryHistory diamondRead ∧
                          UnaryHistory confluenceRead ∧
                            UnaryHistory obstructionRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier routeRoute diamondRoute confluenceRoute obstructionRoute boundaryRoute
    confluencePkg boundaryPkg
  have conditional :=
    MetacicConfluenceAuditWitnessCarrier_conditional_boundary
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (substRead := routeRead)
      (diamondRead := diamondRead) (confluenceRead := confluenceRead)
      (bundle := bundle) (pkg := pkg) carrier routeRoute diamondRoute confluenceRoute
      confluencePkg
  have nonescape :=
    MetacicConfluenceAuditWitnessNonescape
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (obstructionRead := obstructionRead)
      (boundaryRead := boundaryRead) (bundle := bundle) (pkg := pkg) carrier
      obstructionRoute boundaryRoute boundaryPkg
  obtain ⟨_parallelUnary, _substitutionUnary, _diamondUnary, _confluenceUnary,
    routeReadUnary, diamondReadUnary, confluenceReadUnary, _routeRoute,
    _diamondRouteOut, _confluenceRouteOut, _confluencePkgOut⟩ := conditional
  obtain ⟨_obstructionUnary, obstructionReadUnary, boundaryReadUnary, _obstructionRouteOut,
    _boundaryRouteOut, _namePkg, _boundaryPkgOut⟩ := nonescape
  exact
    ⟨carrier.right.right.right.right.right.right.right.right.right.right.right.right.right,
      routeReadUnary, diamondReadUnary, confluenceReadUnary, obstructionReadUnary,
      boundaryReadUnary⟩

theorem MetacicConfluenceAuditWitness_obligation_closure_package [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name routeRead
      diamondRead confluenceRead obstructionRead boundaryRead final : BHist}
    {steps : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence obstruction
        component route ledger name bundle pkg →
      Cont parallel substitution routeRead →
        Cont routeRead diamond diamondRead →
          Cont diamondRead confluence confluenceRead →
            Cont obstruction component obstructionRead →
              Cont obstructionRead route boundaryRead →
                (forall step : BHist, List.Mem step steps -> UnaryHistory step) →
                  final = List.foldl append boundaryRead steps →
                    PkgSig bundle confluenceRead pkg →
                      PkgSig bundle boundaryRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row name)
                            (fun row : BHist =>
                              hsame row parallel ∨ hsame row substitution ∨
                                hsame row diamond ∨ hsame row confluence ∨ hsame row name)
                            (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
                            hsame ∧
                          UnaryHistory final ∧
                            UnaryHistory obstruction ∧
                              Cont routeRead diamond diamondRead ∧
                                Cont diamondRead confluence confluenceRead ∧
                                  Cont obstructionRead route boundaryRead ∧
                                    PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier routeRoute diamondRoute confluenceRoute obstructionRoute boundaryRoute
    stepsUnary finalEq confluencePkg boundaryPkg
  have obligations :=
    MetacicConfluenceAuditWitness_namecert_obligations
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (routeRead := routeRead)
      (diamondRead := diamondRead) (confluenceRead := confluenceRead)
      (obstructionRead := obstructionRead) (boundaryRead := boundaryRead)
      (bundle := bundle) (pkg := pkg) carrier routeRoute diamondRoute confluenceRoute
      obstructionRoute boundaryRoute confluencePkg boundaryPkg
  have localBoundary :=
    MetacicConfluenceAuditWitness_local_diamond_boundary
      (parallel := parallel) (substitution := substitution) (diamond := diamond)
      (confluence := confluence) (obstruction := obstruction) (component := component)
      (route := route) (ledger := ledger) (name := name) (routeRead := routeRead)
      (obstructionRead := obstructionRead) (boundaryRead := boundaryRead)
      (diamondRead := diamondRead) (confluenceRead := confluenceRead) (final := final)
      (steps := steps) (bundle := bundle) (pkg := pkg) carrier routeRoute diamondRoute
      confluenceRoute obstructionRoute boundaryRoute stepsUnary finalEq confluencePkg
      boundaryPkg
  obtain ⟨cert, _routeReadUnary, _diamondReadUnary, _confluenceReadUnary,
    _obstructionReadUnary, _boundaryReadUnary⟩ := obligations
  obtain ⟨_confluenceReadUnaryOut, finalUnary, obstructionUnary, diamondRouteOut,
    confluenceRouteOut, boundaryRouteOut, _confluencePkgOut, _boundaryPkgOut⟩ :=
    localBoundary
  exact
    ⟨cert, finalUnary, obstructionUnary, diamondRouteOut, confluenceRouteOut,
      boundaryRouteOut,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.MetacicConfluenceAuditWitnessUp
