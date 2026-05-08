import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.EllipticCurveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp

theorem EllipticCurveCarrierPacket_field_source_obligation [AskSetup] [PackageSetup]
    {fieldCoeff cubic discriminant : BHist} {tokenBundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FieldSingletonCarrier fieldCoeff ->
      UnaryHistory cubic ->
        Cont fieldCoeff cubic discriminant ->
          TokIntro tokenBundle discriminant pkg ->
            UnaryHistory discriminant ∧ FieldSingletonCarrier fieldCoeff ∧
              hsame fieldCoeff BHist.Empty ∧ TokIntro tokenBundle discriminant pkg ∧
                Cont fieldCoeff cubic discriminant := by
  intro fieldCarrier cubicUnary discriminantCont token
  have fieldUnary : UnaryHistory fieldCoeff :=
    unary_transport unary_empty (hsame_symm fieldCarrier)
  have discriminantUnary : UnaryHistory discriminant :=
    unary_cont_closed fieldUnary cubicUnary discriminantCont
  exact And.intro discriminantUnary
      (And.intro fieldCarrier
        (And.intro fieldCarrier
          (And.intro token discriminantCont)))

def EllipticCurveCarrierPacket
    (field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist) : Prop :=
  UnaryHistory field ∧ UnaryHistory projective ∧ UnaryHistory coeffs ∧
    UnaryHistory basePoint ∧ Cont field projective fieldLedger ∧
      Cont coeffs cubic projectiveLedger ∧ Cont smooth basePoint provenance

theorem EllipticCurveCarrierPacket_field_projective_source_rows
    {field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      UnaryHistory field ∧ UnaryHistory projective ∧ UnaryHistory coeffs ∧
        UnaryHistory basePoint ∧ hsame fieldLedger (append field projective) ∧
          hsame projectiveLedger (append coeffs cubic) ∧
            hsame provenance (append smooth basePoint) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
           (And.intro packet.right.right.right.right.left
             (And.intro packet.right.right.right.right.right.left
               packet.right.right.right.right.right.right)))))

end BEDC.Derived.EllipticCurveUp
