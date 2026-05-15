import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContextFreeGrammarPacket [AskSetup] [PackageSetup]
    (terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory terminal ∧ UnaryHistory nonterminal ∧ UnaryHistory start ∧
    UnaryHistory production ∧ UnaryHistory yield ∧ UnaryHistory derivation ∧
      UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory endpoint ∧
          Cont terminal nonterminal start ∧ Cont production yield readback ∧
            Cont derivation transport route ∧ Cont route provenance name ∧
              Cont name endpoint endpoint ∧ PkgSig bundle endpoint pkg

theorem ContextFreeGrammarPacket_production_stability [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint production' yield' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      hsame production production' ->
        hsame yield yield' ->
          Cont production' yield' readback' ->
            UnaryHistory production' ∧ UnaryHistory yield' ∧ UnaryHistory readback' ∧
              hsame readback readback' ∧ Cont production' yield' readback' ∧
                PkgSig bundle endpoint pkg := by
  intro packet sameProduction sameYield transportedRow
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, productionUnary, yieldUnary,
    _derivationUnary, readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _startRow, productionRow, _routeRow, _nameRow,
    _endpointRow, pkgSig⟩ := packet
  have productionUnary' : UnaryHistory production' :=
    unary_transport productionUnary sameProduction
  have yieldUnary' : UnaryHistory yield' :=
    unary_transport yieldUnary sameYield
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameProduction sameYield productionRow transportedRow
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  exact ⟨productionUnary', yieldUnary', readbackUnary', sameReadback, transportedRow, pkgSig⟩

theorem ContextFreeGrammarPacket_terminal_yield_window [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance name
      endpoint production' yield' readback' derivation' transport' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      hsame production production' ->
        hsame yield yield' ->
          Cont production' yield' readback' ->
            hsame derivation derivation' ->
              hsame transport transport' ->
                Cont derivation' transport' route' ->
                  UnaryHistory readback' ∧ UnaryHistory route' ∧ hsame readback readback' ∧
                    hsame route route' ∧ Cont production' yield' readback' ∧
                      Cont derivation' transport' route' ∧ PkgSig bundle endpoint pkg := by
  intro packet sameProduction sameYield productionRow' sameDerivation sameTransport routeRow'
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, productionUnary, yieldUnary,
    derivationUnary, readbackUnary, transportUnary, routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _startRow, productionRow, routeRow, _nameRow,
    _endpointRow, pkgSig⟩ := packet
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameProduction sameYield productionRow productionRow'
  have readbackUnary' : UnaryHistory readback' := unary_transport readbackUnary sameReadback
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameDerivation sameTransport routeRow routeRow'
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  exact
    ⟨readbackUnary', routeUnary', sameReadback, sameRoute, productionRow', routeRow', pkgSig⟩

theorem ContextFreeGrammarPacket_derivation_concatenation [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint leftSegment rightSegment joined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      Cont derivation transport leftSegment ->
        Cont leftSegment route rightSegment ->
          Cont rightSegment endpoint joined ->
            PkgSig bundle joined pkg ->
              UnaryHistory leftSegment ∧ UnaryHistory rightSegment ∧ UnaryHistory joined ∧
                Cont derivation transport leftSegment ∧ Cont leftSegment route rightSegment ∧
                  Cont rightSegment endpoint joined ∧ PkgSig bundle joined pkg ∧
                    PkgSig bundle endpoint pkg := by
  intro packet derivationTransportLeft leftRouteRight rightEndpointJoined joinedPkg
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, _productionUnary, _yieldUnary,
    derivationUnary, _readbackUnary, transportUnary, routeUnary, _provenanceUnary,
    _nameUnary, endpointUnary, _terminalNonterminalStart, _productionYieldReadback,
    _derivationTransportRoute, _routeProvenanceName, _nameEndpointEndpoint,
    endpointPkg⟩ := packet
  have leftUnary : UnaryHistory leftSegment :=
    unary_cont_closed derivationUnary transportUnary derivationTransportLeft
  have rightUnary : UnaryHistory rightSegment :=
    unary_cont_closed leftUnary routeUnary leftRouteRight
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed rightUnary endpointUnary rightEndpointJoined
  exact
    ⟨leftUnary, rightUnary, joinedUnary, derivationTransportLeft, leftRouteRight,
      rightEndpointJoined, joinedPkg, endpointPkg⟩

theorem ContextFreeGrammarPacket_yield_readback [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint finalYield : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      Cont derivation readback finalYield ->
        UnaryHistory start ∧ UnaryHistory production ∧ UnaryHistory derivation ∧
          UnaryHistory readback ∧ UnaryHistory yield ∧ UnaryHistory finalYield ∧
            Cont derivation readback finalYield ∧ PkgSig bundle endpoint pkg := by
  intro packet finalYieldRow
  obtain ⟨_terminalUnary, _nonterminalUnary, startUnary, productionUnary, yieldUnary,
    derivationUnary, readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _startRow, _productionRow, _routeRow, _nameRow,
    _endpointRow, pkgSig⟩ := packet
  have finalYieldUnary : UnaryHistory finalYield :=
    unary_cont_closed derivationUnary readbackUnary finalYieldRow
  exact ⟨startUnary, productionUnary, derivationUnary, readbackUnary, yieldUnary,
    finalYieldUnary, finalYieldRow, pkgSig⟩

theorem ContextFreeGrammarPacket_parse_tree_derivation_boundary [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint tree routeBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      UnaryHistory tree ->
        Cont derivation tree routeBoundary ->
          Cont routeBoundary readback endpoint ->
            UnaryHistory routeBoundary ∧ UnaryHistory endpoint ∧
              Cont derivation tree routeBoundary ∧ Cont routeBoundary readback endpoint ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet treeUnary derivationTreeBoundary routeBoundaryReadbackEndpoint
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, _productionUnary, _yieldUnary,
    derivationUnary, readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _startRow, _productionRow, _routeRow, _nameRow,
    _endpointRow, pkgSig⟩ := packet
  have routeBoundaryUnary : UnaryHistory routeBoundary :=
    unary_cont_closed derivationUnary treeUnary derivationTreeBoundary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeBoundaryUnary readbackUnary routeBoundaryReadbackEndpoint
  exact
    ⟨routeBoundaryUnary, endpointUnary, derivationTreeBoundary,
      routeBoundaryReadbackEndpoint, pkgSig⟩

theorem ContextFreeGrammarPacket_consumer_boundary_determinacy [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint terminal' nonterminal' start' production' yield' derivation' readback'
      transport' route' provenance' name' endpoint' boundary boundary' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      ContextFreeGrammarPacket terminal' nonterminal' start' production' yield' derivation'
        readback' transport' route' provenance' name' endpoint' bundle pkg ->
        hsame terminal terminal' ->
          hsame nonterminal nonterminal' ->
            hsame production production' ->
              hsame yield yield' ->
                hsame derivation derivation' ->
                  hsame transport transport' ->
                    hsame name name' ->
                      hsame endpoint endpoint' ->
                        Cont name endpoint boundary ->
                          Cont name' endpoint' boundary' ->
                            PkgSig bundle boundary pkg ->
                              PkgSig bundle boundary' pkg ->
                                hsame start start' ∧ hsame readback readback' ∧
                                  hsame route route' ∧ hsame boundary boundary' ∧
                                    PkgSig bundle boundary pkg ∧
                                      PkgSig bundle boundary' pkg := by
  intro packet packet' sameTerminal sameNonterminal sameProduction sameYield sameDerivation
    sameTransport sameName sameEndpoint boundaryRow boundaryRow' boundaryPkg boundaryPkg'
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, _productionUnary, _yieldUnary,
    _derivationUnary, _readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, startRow, productionRow, routeRow, _nameRow,
    _endpointRow, _pkgSig⟩ := packet
  obtain ⟨_terminalUnary', _nonterminalUnary', _startUnary', _productionUnary', _yieldUnary',
    _derivationUnary', _readbackUnary', _transportUnary', _routeUnary', _provenanceUnary',
    _nameUnary', _endpointUnary', startRow', productionRow', routeRow', _nameRow',
    _endpointRow', _pkgSig'⟩ := packet'
  have sameStart : hsame start start' :=
    cont_respects_hsame sameTerminal sameNonterminal startRow startRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameProduction sameYield productionRow productionRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameDerivation sameTransport routeRow routeRow'
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameName sameEndpoint boundaryRow boundaryRow'
  exact
    ⟨sameStart, sameReadback, sameRoute, sameBoundary, boundaryPkg, boundaryPkg'⟩

theorem ContextFreeGrammarPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
            transport route provenance name endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
            transport route provenance name endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
            transport route provenance name endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem ContextFreeGrammarPacket_regularlanguage_turingmachine_bridge_boundary [AskSetup]
    [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
      transport route provenance name endpoint bundle pkg ->
      Cont endpoint name consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory terminal ∧ UnaryHistory nonterminal ∧ UnaryHistory start ∧
            UnaryHistory production ∧ UnaryHistory yield ∧ UnaryHistory derivation ∧
              UnaryHistory readback ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
                UnaryHistory consumer ∧ Cont terminal nonterminal start ∧
                  Cont production yield readback ∧ Cont derivation transport route ∧
                    Cont route provenance name ∧ Cont endpoint name consumer ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet endpointNameConsumer consumerPkg
  obtain ⟨terminalUnary, nonterminalUnary, startUnary, productionUnary, yieldUnary,
    derivationUnary, readbackUnary, _transportUnary, routeUnary, _provenanceUnary,
    nameUnary, endpointUnary, terminalNonterminalStart, productionYieldReadback,
    derivationTransportRoute, routeProvenanceName, _nameEndpointEndpoint,
    endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary nameUnary endpointNameConsumer
  exact
    ⟨terminalUnary, nonterminalUnary, startUnary, productionUnary, yieldUnary,
      derivationUnary, readbackUnary, routeUnary, endpointUnary, consumerUnary,
      terminalNonterminalStart, productionYieldReadback, derivationTransportRoute,
      routeProvenanceName, endpointNameConsumer, endpointPkg, consumerPkg⟩

theorem ContextFreeGrammarPacket_derivation_prefix_carrier [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint prefixRow suffix split prefixRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      Cont start prefixRow split ->
        Cont split suffix derivation ->
          Cont prefixRow transport prefixRoute ->
            PkgSig bundle prefixRoute pkg ->
              UnaryHistory start ∧ UnaryHistory production ∧ UnaryHistory prefixRow ∧
                UnaryHistory split ∧ UnaryHistory prefixRoute ∧ Cont start prefixRow split ∧
                  Cont prefixRow transport prefixRoute ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle prefixRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet startPrefixSplit splitSuffixDerivation prefixTransportRoute prefixPkg
  obtain ⟨_terminalUnary, _nonterminalUnary, startUnary, productionUnary, _yieldUnary,
    derivationUnary, _readbackUnary, transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _terminalNonterminalStart, _productionYieldReadback,
    _derivationTransportRoute, _routeProvenanceName, _nameEndpointEndpoint,
    endpointPkg⟩ := packet
  have splitUnary : UnaryHistory split :=
    unary_cont_left_factor splitSuffixDerivation derivationUnary
  have prefixUnary : UnaryHistory prefixRow :=
    unary_cont_right_factor startPrefixSplit splitUnary
  have prefixRouteUnary : UnaryHistory prefixRoute :=
    unary_cont_closed prefixUnary transportUnary prefixTransportRoute
  exact
    ⟨startUnary, productionUnary, prefixUnary, splitUnary, prefixRouteUnary,
      startPrefixSplit, prefixTransportRoute, endpointPkg, prefixPkg⟩

end BEDC.Derived.ContextFreeGrammarUp
