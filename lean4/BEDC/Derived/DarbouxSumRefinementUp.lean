import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

inductive DarbouxSumRefinementUp : Type where
  | mk (I P Q L U M D C E H K G N : BHist) : DarbouxSumRefinementUp
  deriving DecidableEq

namespace DarbouxSumRefinementUp

def DarbouxSumRefinementCarrier
    (I P Q L U M D C E H K G N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory I ∧
    UnaryHistory P ∧
      UnaryHistory Q ∧
        UnaryHistory L ∧
          UnaryHistory U ∧
            UnaryHistory M ∧
              UnaryHistory D ∧
                UnaryHistory C ∧
                  UnaryHistory E ∧
                    UnaryHistory H ∧
                      UnaryHistory K ∧
                        UnaryHistory G ∧
                          UnaryHistory N ∧ hsame H (append P Q)

theorem DarbouxSumRefinementCarrier_namecert_obligations
    {I P Q L U M D C E H K G N readinessRead sealRead : BHist} :
    DarbouxSumRefinementCarrier I P Q L U M D C E H K G N ->
      Cont D C readinessRead ->
        Cont readinessRead E sealRead ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row P ∨ hsame row Q ∨ hsame row L ∨ hsame row U ∨
                  hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                    hsame row H ∨ hsame row K ∨ hsame row G ∨ hsame row N ∨
                      hsame row sealRead)
              (fun row : BHist =>
                hsame row sealRead ∧ Cont D C readinessRead ∧
                  Cont readinessRead E sealRead)
              hsame ∧ UnaryHistory readinessRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier darbouxsReadiness readinessSeal
  obtain ⟨_intervalUnary, _sourcePartitionUnary, _refinedPartitionUnary, _lowerUnary,
    _upperUnary, _monotonicityUnary, darbouxsUnary, cauchyUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _componentTransport⟩ :=
      carrier
  have readinessUnary : UnaryHistory readinessRead :=
    unary_cont_closed darbouxsUnary cauchyUnary darbouxsReadiness
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readinessUnary sealUnary readinessSeal
  refine ⟨?_, readinessUnary, sealReadUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealReadUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.left, darbouxsReadiness, readinessSeal⟩

theorem DarbouxSumRefinementCarrier_cauchy_handoff
    {I P Q L U M D C E H K G N lowerUpperRead readinessRead sealRead : BHist} :
    DarbouxSumRefinementCarrier I P Q L U M D C E H K G N ->
      Cont L U lowerUpperRead ->
        Cont lowerUpperRead D readinessRead ->
          Cont readinessRead E sealRead ->
            UnaryHistory lowerUpperRead ∧
              UnaryHistory readinessRead ∧
                UnaryHistory sealRead ∧
                  hsame H (append P Q) ∧
                    Cont L U lowerUpperRead ∧
                      Cont lowerUpperRead D readinessRead ∧
                        Cont readinessRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier lowerUpperRoute lowerUpperDarbouxsRoute readinessSeal
  obtain ⟨_intervalUnary, _sourcePartitionUnary, _refinedPartitionUnary, lowerUnary,
    upperUnary, _monotonicityUnary, darbouxsUnary, _cauchyUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, componentTransport⟩ :=
      carrier
  have lowerUpperUnary : UnaryHistory lowerUpperRead :=
    unary_cont_closed lowerUnary upperUnary lowerUpperRoute
  have readinessUnary : UnaryHistory readinessRead :=
    unary_cont_closed lowerUpperUnary darbouxsUnary lowerUpperDarbouxsRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readinessUnary sealUnary readinessSeal
  exact
    ⟨lowerUpperUnary, readinessUnary, sealReadUnary, componentTransport,
      lowerUpperRoute, lowerUpperDarbouxsRoute, readinessSeal⟩

end DarbouxSumRefinementUp

end BEDC.Derived
