import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_topology_consumer_boundary [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported topologyRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont topology openLeft topologyRead →
        Cont topologyRead openRight consumerRead →
          PkgSig bundle consumerRead pkg →
            UnaryHistory topology ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
              UnaryHistory topologyRead ∧ UnaryHistory consumerRead ∧
                Cont topology openLeft topologyRead ∧
                  Cont topologyRead openRight consumerRead ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet topologyRoute consumerRoute consumerPkg
  have topologyReadUnary : UnaryHistory topologyRead :=
    unary_cont_closed packet.left packet.right.right.right.right.left topologyRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed topologyReadUnary packet.right.right.right.right.right.left consumerRoute
  exact
    ⟨packet.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      topologyReadUnary,
      consumerReadUnary,
      topologyRoute,
      consumerRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      consumerPkg⟩

end BEDC.Derived.NormalSpaceUp
