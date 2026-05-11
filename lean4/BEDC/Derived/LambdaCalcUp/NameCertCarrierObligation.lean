import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LambdaCalcBHistTermPacketCarrier_namecert_carrier_obligation
    {graph edge connected acyclic tag payload endpoint : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      SemanticNameCert
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        hsame ∧
        UnaryHistory payload ∧ UnaryHistory endpoint ∧ Cont tag payload endpoint := by
  intro packet
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        (fun row : BHist =>
          LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint packet
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro _left _right same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeftMiddle sameMiddleRight
        exact hsame_trans sameLeftMiddle sameMiddleRight
      carrier_respects_equiv := by
        intro left right sameEndpoint carrierLeft
        exact
          (LambdaCalcBHistTermPacketCarrier_public_endpoint_transport carrierLeft
            (hsame_refl tag) sameEndpoint).left
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro packet.right.left
      (And.intro packet.right.right.left packet.right.right.right))

end BEDC.Derived.LambdaCalcUp
