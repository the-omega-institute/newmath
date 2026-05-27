import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_closed_set_separation_route [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported separationRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont disjoint transport separationRead →
        Cont separationRead replay routeRead →
          PkgSig bundle routeRead pkg →
            UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
              UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
                UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory separationRead ∧
                  UnaryHistory routeRead ∧ Cont closedLeft closedRight disjoint ∧
                    Cont disjoint transport separationRead ∧
                      Cont separationRead replay routeRead ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet separationRoute routeReplay routePkg
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed packet.right.right.right.left
      packet.right.right.right.right.right.right.left separationRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed separationUnary packet.right.right.right.right.right.right.right.left
      routeReplay
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      separationUnary,
      routeUnary,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      separationRoute,
      routeReplay,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      routePkg⟩

end BEDC.Derived.NormalSpaceUp
