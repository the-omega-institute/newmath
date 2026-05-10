import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LambdaCalcBHistTermPacketCarrier_substitution_ledger_obligation
    {graph edge connected acyclic tag payload endpoint substTag substPayload substEndpoint
      varIndex ledger resultPayload : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic substTag substPayload
          substEndpoint ->
        UnaryHistory varIndex ->
          Cont endpoint substEndpoint ledger ->
            Cont ledger varIndex resultPayload ->
              SemanticNameCert
                  (fun row : BHist =>
                    exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                  (fun row : BHist =>
                    exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                  (fun row : BHist =>
                    exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                  hsame ∧
                UnaryHistory ledger ∧ UnaryHistory resultPayload ∧
                  hsame resultPayload (append (append endpoint substEndpoint) varIndex) ∧
                    (forall resultPayload' : BHist,
                      Cont ledger varIndex resultPayload' -> hsame resultPayload resultPayload') := by
  intro packet substPacket varUnary ledgerRow resultRow
  have scope :=
    LambdaCalcBHistTermPacketCarrier_substitution_ledger_scope packet substPacket varUnary
      ledgerRow resultRow
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
        (fun row : BHist =>
          exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
        (fun row : BHist =>
          exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro resultPayload
          (Exists.intro ledger (And.intro ledgerRow resultRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same source
        cases source with
        | intro l rows =>
            exact Exists.intro l
              (And.intro rows.left (cont_result_hsame_transport rows.right same))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  have resultDeterminacy :
      forall resultPayload' : BHist,
        Cont ledger varIndex resultPayload' -> hsame resultPayload resultPayload' := by
    intro resultPayload' resultRow'
    exact cont_deterministic resultRow resultRow'
  exact And.intro cert
    (And.intro scope.left
      (And.intro scope.right.left
        (And.intro scope.right.right.right resultDeterminacy)))

end BEDC.Derived.LambdaCalcUp
