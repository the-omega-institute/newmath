import BEDC.Derived.DyadicIntervalUp

namespace BEDC.Derived.DyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalPacket_public_regseq_real_bridge [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint left' right' width' midpoint'
      radius' order' provenance' endpoint' sealRow windowRow regseqRead realRead : BHist}
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
                            Cont windowRow endpoint' regseqRead ->
                              Cont regseqRead radius' realRead ->
                                PkgSig bundle realRead pkg ->
                                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                                    hsame width width' ∧ hsame radius radius' ∧
                                      PkgSig bundle realRead pkg := by
  intro packet sameLeft sameRight sameProvenance widthRow' midpointRow' radiusRow' orderRow'
    endpointRow' endpointPkg sealCont windowCont regseqCont realCont realPkg
  have refined :=
    DyadicIntervalPacket_nested_refinement_ledger packet sameLeft sameRight sameProvenance
      widthRow' midpointRow' radiusRow' orderRow' endpointRow' endpointPkg
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed refined.left.right.right.right.right.right.right.right.left
      refined.left.right.right.left sealCont
  have windowUnary : UnaryHistory windowRow :=
    unary_cont_closed sealUnary refined.left.right.right.right.right.left windowCont
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary refined.left.right.right.right.right.right.right.right.left
      regseqCont
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary refined.left.right.right.right.right.left realCont
  exact
    And.intro regseqUnary
      (And.intro realUnary
        (And.intro refined.right.left
          (And.intro refined.right.right.right.left realPkg)))

theorem DyadicIntervalPacket_standard_interval_bridge_boundary [AskSetup] [PackageSetup]
    {left right width midpoint radius order provenance endpoint sealRow standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalPacket left right width midpoint radius order provenance endpoint bundle pkg ->
      Cont endpoint width sealRow ->
        Cont sealRow radius standardRead ->
          PkgSig bundle standardRead pkg ->
            UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory width ∧ UnaryHistory radius ∧
              UnaryHistory standardRead ∧ hsame sealRow (append endpoint width) ∧
                hsame standardRead (append sealRow radius) ∧ PkgSig bundle standardRead pkg := by
  intro packet sealCont standardCont standardPkg
  obtain ⟨leftUnary, rightUnary, widthUnary, _midpointUnary, radiusUnary, _orderUnary,
    _provenanceUnary, endpointUnary, _widthRow, _midpointRow, _radiusRow, _orderRow,
    _endpointRow, _pkgRow⟩ := packet
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed endpointUnary widthUnary sealCont
  have standardUnary : UnaryHistory standardRead :=
    unary_cont_closed sealUnary radiusUnary standardCont
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro widthUnary
          (And.intro radiusUnary
            (And.intro standardUnary
              (And.intro sealCont
                (And.intro standardCont standardPkg))))))

end BEDC.Derived.DyadicIntervalUp
