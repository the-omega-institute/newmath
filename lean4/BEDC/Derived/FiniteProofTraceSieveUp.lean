import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FiniteProofTraceSieveUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def FiniteProofTraceSieveCarrier (T E D O H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory T ∧ UnaryHistory E ∧ UnaryHistory D ∧ UnaryHistory O ∧
    Cont T E D ∧ Cont D O C ∧ Cont C P N

theorem FiniteProofTraceSieveFrontierHandoff
    {T E D O H C P N endpointRead dischargeRead frontierRead : BHist} :
    FiniteProofTraceSieveCarrier T E D O H C P N ->
      Cont T E endpointRead ->
        Cont endpointRead D dischargeRead ->
          Cont dischargeRead O frontierRead ->
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row T ∨ hsame row E ∨ hsame row D ∨ hsame row O ∨
                    hsame row endpointRead ∨ hsame row dischargeRead ∨
                      hsame row frontierRead)
                (fun row : BHist =>
                  hsame row frontierRead ∧ Cont T E endpointRead ∧
                    Cont endpointRead D dischargeRead ∧
                      Cont dischargeRead O frontierRead)
                hsame ∧
              UnaryHistory endpointRead ∧ UnaryHistory dischargeRead ∧
                UnaryHistory frontierRead ∧ Cont T E endpointRead ∧
                  Cont endpointRead D dischargeRead ∧
                    Cont dischargeRead O frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier endpointRoute dischargeRoute frontierRoute
  obtain ⟨tUnary, eUnary, dUnary, oUnary, _carrierEndpoint, _carrierDischarge,
    _carrierFrontier⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed tUnary eUnary endpointRoute
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed endpointUnary dUnary dischargeRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed dischargeUnary oUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row E ∨ hsame row D ∨ hsame row O ∨
              hsame row endpointRead ∨ hsame row dischargeRead ∨
                hsame row frontierRead)
          (fun row : BHist =>
            hsame row frontierRead ∧ Cont T E endpointRead ∧
              Cont endpointRead D dischargeRead ∧ Cont dischargeRead O frontierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointRoute, dischargeRoute, frontierRoute⟩
  }
  exact
    ⟨cert, endpointUnary, dischargeUnary, frontierUnary, endpointRoute, dischargeRoute,
      frontierRoute⟩

end BEDC.Derived.FiniteProofTraceSieveUp
