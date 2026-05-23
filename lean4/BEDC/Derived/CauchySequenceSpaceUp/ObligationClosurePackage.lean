import BEDC.Derived.CauchySequenceSpaceUp.WindowFactorization

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name windowRead completionRead
      routeRead handoff sealRow inventory tail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont family schedule windowRead ->
        Cont windowRead tolerance completionRead ->
          Cont completionRead transport routeRead ->
            Cont route name handoff ->
              Cont handoff completion sealRow ->
                Cont sealRow route inventory ->
                  Cont inventory tolerance tail ->
                    PkgSig bundle routeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            CauchySequenceSpaceCarrier family schedule window tolerance
                              completion transport route name bundle pkg ∧ hsame row completion)
                          (fun row : BHist =>
                            CauchySequenceSpaceCarrier family schedule window tolerance
                              completion transport route name bundle pkg ∧ hsame row completion)
                          (fun row : BHist =>
                            CauchySequenceSpaceCarrier family schedule window tolerance
                              completion transport route name bundle pkg ∧ hsame row completion)
                          hsame ∧
                        CauchySequenceSpaceCarrier family schedule windowRead tolerance
                          completionRead transport routeRead name bundle pkg ∧
                          UnaryHistory tail ∧ hsame window windowRead ∧
                            hsame completion completionRead ∧ hsame route routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier familyScheduleWindowRead windowReadToleranceCompletionRead
    completionReadTransportRouteRead routeNameHandoff handoffCompletionSeal sealRouteInventory
    inventoryToleranceTail routeReadPkg
  have regular :
      CauchySequenceSpaceCarrier family schedule windowRead tolerance completionRead transport
          routeRead name bundle pkg ∧
        hsame window windowRead ∧ hsame completion completionRead ∧ hsame route routeRead :=
    CauchySequenceSpaceCarrier_regular_window_factorization carrier familyScheduleWindowRead
      windowReadToleranceCompletionRead completionReadTransportRouteRead routeReadPkg
  have tailPackage :
      SemanticNameCert
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          hsame ∧
        UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory inventory ∧
          UnaryHistory tail ∧ Cont route name handoff ∧ Cont handoff completion sealRow ∧
            Cont sealRow route inventory ∧ Cont inventory tolerance tail ∧
              PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    CauchySequenceSpaceCarrier_tail_window_factorization carrier routeNameHandoff
      handoffCompletionSeal sealRouteInventory inventoryToleranceTail
  exact
    ⟨tailPackage.left, regular.left, tailPackage.right.right.right.right.left,
      regular.right.left, regular.right.right.left, regular.right.right.right⟩

end BEDC.Derived.CauchySequenceSpaceUp
