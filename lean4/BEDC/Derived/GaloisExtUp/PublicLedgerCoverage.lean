import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.SeparableExtUp

theorem GaloisExtSourcePacket_public_ledger_coverage [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint automorphism fixedBase action
      automorphismLedger orbitLedger orbitEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      UnaryHistory automorphism ->
        Cont fieldExt automorphism fixedBase ->
          Cont fixedBase normality action ->
            Cont action provenance automorphismLedger ->
              Cont normality provenance orbitLedger ->
                Cont orbitLedger separability orbitEndpoint ->
                  SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
                      sepProvenance separable bundle pkg ∧
                    UnaryHistory fixedBase ∧ UnaryHistory action ∧
                      UnaryHistory automorphismLedger ∧ UnaryHistory orbitLedger ∧
                        UnaryHistory orbitEndpoint ∧
                          hsame automorphismLedger (append action provenance) ∧
                            hsame orbitEndpoint
                              (append (append normality provenance) separability) ∧
                              PkgSig bundle endpoint pkg := by
  intro packet automorphismUnary fixedBaseCont actionCont automorphismLedgerCont orbitLedgerCont
    orbitEndpointCont
  have dependencyRows :=
    GaloisExtSourcePacket_dependency_exactness_ledger packet
  have fixedBaseUnary : UnaryHistory fixedBase :=
    unary_cont_closed packet.left.left automorphismUnary fixedBaseCont
  have actionUnary : UnaryHistory action :=
    unary_cont_closed fixedBaseUnary packet.right.left actionCont
  have automorphismLedgerUnary : UnaryHistory automorphismLedger :=
    unary_cont_closed actionUnary dependencyRows.left automorphismLedgerCont
  have orbitLedgerUnary : UnaryHistory orbitLedger :=
    unary_cont_closed packet.right.left dependencyRows.left orbitLedgerCont
  have orbitEndpointUnary : UnaryHistory orbitEndpoint :=
    unary_cont_closed orbitLedgerUnary packet.right.right.left orbitEndpointCont
  have orbitEndpointReadback :
      hsame orbitEndpoint (append (append normality provenance) separability) :=
    hsame_trans orbitEndpointCont
      (congrArg (fun h : BHist => append h separability) orbitLedgerCont)
  exact And.intro packet.left
    (And.intro fixedBaseUnary
      (And.intro actionUnary
        (And.intro automorphismLedgerUnary
          (And.intro orbitLedgerUnary
            (And.intro orbitEndpointUnary
              (And.intro automorphismLedgerCont
                (And.intro orbitEndpointReadback
                  dependencyRows.right.right.right.right.right.right)))))))

end BEDC.Derived.GaloisExtUp
