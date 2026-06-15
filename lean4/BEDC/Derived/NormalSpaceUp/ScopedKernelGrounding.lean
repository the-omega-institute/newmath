import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_scoped_kernel_grounding [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported topologyRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont topology openLeft topologyRead →
        Cont topologyRead openRight boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
              UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
                UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
                  UnaryHistory localName ∧ UnaryHistory exported ∧
                    UnaryHistory topologyRead ∧ UnaryHistory boundaryRead ∧
                      Cont closedLeft closedRight disjoint ∧
                        Cont openLeft openRight transport ∧
                          Cont transport replay provenance ∧
                            Cont provenance localName exported ∧
                              Cont topology openLeft topologyRead ∧
                                Cont topologyRead openRight boundaryRead ∧
                                  PkgSig bundle localName pkg ∧
                                    PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet topologyRoute boundaryRoute boundaryPkg
  obtain
    ⟨topologyUnary, closedLeftUnary, closedRightUnary, disjointUnary, openLeftUnary,
      openRightUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
      exportedUnary, closedRoute, openRoute, transportRoute, exportRoute,
      localPkg⟩ := packet
  have topologyReadUnary : UnaryHistory topologyRead :=
    unary_cont_closed topologyUnary openLeftUnary topologyRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed topologyReadUnary openRightUnary boundaryRoute
  exact
    ⟨topologyUnary, closedLeftUnary, closedRightUnary, disjointUnary, openLeftUnary,
      openRightUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
      exportedUnary, topologyReadUnary, boundaryReadUnary, closedRoute, openRoute,
      transportRoute, exportRoute, topologyRoute, boundaryRoute, localPkg, boundaryPkg⟩

end BEDC.Derived.NormalSpaceUp
