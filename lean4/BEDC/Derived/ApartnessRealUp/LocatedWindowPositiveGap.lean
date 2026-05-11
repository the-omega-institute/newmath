import BEDC.Derived.ApartnessRealUp

namespace BEDC.Derived.ApartnessRealUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApartnessRealSeparationPacket_located_window_positive_gap_handoff
    [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint
      reverseLedger pkgrow consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      PositiveUnaryDenominator radius ->
        Cont rightReadback leftReadback reverseLedger ->
          Cont separation reverseLedger pkgrow ->
            Cont reverseLedger separation pkgrow ->
              PkgSig bundle pkgrow pkg ->
                Cont pkgrow radius consumerRow ->
                  PkgSig bundle consumerRow pkg ->
                    ApartnessRealSeparationPacket left right radius window leftReadback
                        rightReadback separation reverseLedger pkgrow bundle pkg ∧
                      UnaryHistory consumerRow ∧ hsame consumerRow (append pkgrow radius) := by
  intro packet positiveRadius reverseLedgerRow forwardPkgRow reversePkgRow pkgSig consumerRowCont
    _consumerPkg
  have radiusUnary : UnaryHistory radius :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveRadius).left
  have leftReadbackUnary : UnaryHistory leftReadback :=
    unary_cont_closed packet.left packet.right.right.right.left
      packet.right.right.right.right.right.left
  have rightReadbackUnary : UnaryHistory rightReadback :=
    unary_cont_closed packet.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.left
  have separationPacket :
      ApartnessRealSeparationPacket left right radius window leftReadback rightReadback
          separation reverseLedger pkgrow bundle pkg :=
    And.intro positiveRadius
      (And.intro packet.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.left
            (And.intro reverseLedgerRow
              (And.intro forwardPkgRow
                (And.intro reversePkgRow pkgSig))))))
  have pkgrowUnary : UnaryHistory pkgrow :=
    unary_cont_closed
      (unary_cont_closed leftReadbackUnary rightReadbackUnary
        packet.right.right.right.right.right.right.right.left)
      (unary_cont_closed rightReadbackUnary leftReadbackUnary reverseLedgerRow) forwardPkgRow
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed pkgrowUnary radiusUnary consumerRowCont
  exact And.intro separationPacket (And.intro consumerUnary consumerRowCont)

end BEDC.Derived.ApartnessRealUp
