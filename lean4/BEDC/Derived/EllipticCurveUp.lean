import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.EllipticCurveUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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
