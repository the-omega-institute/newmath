import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_ledger_route_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n selected routed ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame selected a ∨ hsame selected b ∨ hsame selected c ∨ hsame selected d ∨
          hsame selected e ∨ hsame selected f ∨ hsame selected g) ->
        Cont selected h routed ->
          Cont routed p ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory selected ∧ UnaryHistory routed ∧ UnaryHistory ledgerRead ∧
                Cont selected h routed ∧ Cont routed p ledgerRead ∧ hsame p n ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro packet selectedRow selectedRoute ledgerRoute ledgerPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have selectedUnary : UnaryHistory selected := by
    cases selectedRow with
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
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed selectedUnary hUnary selectedRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routedUnary pUnary ledgerRoute
  exact
    ⟨selectedUnary, routedUnary, ledgerUnary, selectedRoute, ledgerRoute,
      sameProvenanceName, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
