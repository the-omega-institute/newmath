import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_cauchyspace_hausdorff_consumer_boundary [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported hausdorffRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont topology transport hausdorffRead →
        Cont hausdorffRead exported cauchyRead →
          PkgSig bundle cauchyRead pkg →
            UnaryHistory topology ∧ UnaryHistory transport ∧ UnaryHistory exported ∧
              UnaryHistory hausdorffRead ∧ UnaryHistory cauchyRead ∧
                Cont closedLeft closedRight disjoint ∧ Cont openLeft openRight transport ∧
                  Cont topology transport hausdorffRead ∧
                    Cont hausdorffRead exported cauchyRead ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet hausdorffRoute cauchyRoute cauchyPkg
  obtain ⟨topologyUnary, _closedLeftUnary, _closedRightUnary, _disjointUnary,
    _openLeftUnary, _openRightUnary, transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, closedDisjoint, openTransport, _transportProvenance,
    _provenanceExported, localNamePkg⟩ := packet
  have hausdorffReadUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed topologyUnary transportUnary hausdorffRoute
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed hausdorffReadUnary exportedUnary cauchyRoute
  exact
    ⟨topologyUnary, transportUnary, exportedUnary, hausdorffReadUnary, cauchyReadUnary,
      closedDisjoint, openTransport, hausdorffRoute, cauchyRoute, localNamePkg, cauchyPkg⟩

end BEDC.Derived.NormalSpaceUp
