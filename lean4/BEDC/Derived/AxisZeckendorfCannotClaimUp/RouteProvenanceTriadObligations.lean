import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_route_provenance_triad_obligations
    [AskSetup] [PackageSetup] {a b c d e f g h p n selected routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame selected a ∨ hsame selected b ∨ hsame selected c ∨ hsame selected d ∨
        hsame selected e ∨ hsame selected f ∨ hsame selected g) ->
        Cont selected p routed ->
          PkgSig bundle p pkg ->
            UnaryHistory selected ∧ UnaryHistory p ∧ Cont selected p routed ∧
              hsame p n ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro packet selectedSource selectedRoute selectedPkg
  obtain ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, _routeAB, _routeCD,
    _routeEF, pUnary, sameProvenanceName, _packetPkg⟩ := packet
  have selectedUnary : UnaryHistory selected := by
    cases selectedSource with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  exact
    ⟨selectedUnary, pUnary, selectedRoute, sameProvenanceName, selectedPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
