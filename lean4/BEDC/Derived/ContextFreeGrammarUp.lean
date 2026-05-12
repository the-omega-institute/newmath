import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.ContextFreeGrammarUp
