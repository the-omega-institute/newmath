import BEDC.Derived.DyadicIntervalUp

namespace BEDC.Derived.DyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalPacket_regular_window_bridge_boundary [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint left' right' width' midpoint'
      radius' order' provenance' endpoint' sealRow windowRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame provenance provenance' ->
            Cont left' right' width' ->
              Cont left' width' midpoint' ->
                Cont right' width' radius' ->
                  Cont midpoint' radius' order' ->
                    Cont order' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        Cont endpoint' width' sealRow ->
                          Cont sealRow radius' windowRow ->
                            PkgSig bundle windowRow pkg ->
                              DyadicIntervalPacket left' right' width' midpoint' radius' order'
                                  provenance' endpoint' bundle pkg ∧
                                UnaryHistory windowRow ∧
                                  hsame windowRow (append endpoint' (append width' radius')) ∧
                                    hsame endpoint endpoint' ∧ PkgSig bundle windowRow pkg := by
  intro packet sameLeft sameRight sameProvenance widthRow' midpointRow' radiusRow' orderRow'
    endpointRow' endpointPkg sealCont windowCont windowPkg
  have refined :=
    DyadicIntervalPacket_nested_refinement_ledger packet sameLeft sameRight sameProvenance
      widthRow' midpointRow' radiusRow' orderRow' endpointRow' endpointPkg
  obtain ⟨_leftUnary, _rightUnary, widthUnary, _midpointUnary, radiusUnary, _orderUnary,
    _provenanceUnary, endpointUnary, _widthCont, _midpointCont, _radiusCont, _orderCont,
    _endpointCont, _pkgSig⟩ := refined.left
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed endpointUnary widthUnary sealCont
  have windowUnary : UnaryHistory windowRow :=
    unary_cont_closed sealUnary radiusUnary windowCont
  have windowBoundary : hsame windowRow (append endpoint' (append width' radius')) := by
    cases sealCont
    cases windowCont
    exact append_assoc endpoint' width' radius'
  exact
    And.intro refined.left
      (And.intro windowUnary
        (And.intro windowBoundary
          (And.intro refined.right.right.right.right.right windowPkg)))

end BEDC.Derived.DyadicIntervalUp
