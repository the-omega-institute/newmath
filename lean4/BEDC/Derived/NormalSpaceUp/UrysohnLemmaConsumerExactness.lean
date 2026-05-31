import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_urysohn_lemma_consumer_exactness [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported separationRead urysohnRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont openLeft openRight separationRead →
        Cont separationRead exported urysohnRead →
          Cont urysohnRead replay boundaryRead →
            PkgSig bundle boundaryRead pkg →
              UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧ UnaryHistory disjoint ∧
                UnaryHistory openLeft ∧ UnaryHistory openRight ∧ UnaryHistory separationRead ∧
                  UnaryHistory urysohnRead ∧ UnaryHistory boundaryRead ∧
                    Cont openLeft openRight separationRead ∧
                      Cont separationRead exported urysohnRead ∧
                        Cont urysohnRead replay boundaryRead ∧
                          PkgSig bundle localName pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet separationRoute urysohnRoute boundaryRoute boundaryPkg
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left separationRoute
  have urysohnUnary : UnaryHistory urysohnRead :=
    unary_cont_closed separationUnary
      packet.right.right.right.right.right.right.right.right.right.right.left urysohnRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed urysohnUnary packet.right.right.right.right.right.right.right.left
      boundaryRoute
  exact
    ⟨packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      separationUnary,
      urysohnUnary,
      boundaryUnary,
      separationRoute,
      urysohnRoute,
      boundaryRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      boundaryPkg⟩

end BEDC.Derived.NormalSpaceUp
