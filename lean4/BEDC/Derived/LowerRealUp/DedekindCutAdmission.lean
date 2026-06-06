import BEDC.Derived.LowerRealUp.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LowerRealCarrier_dedekind_cut_admission
    {L0 W R E H C P N locatedRead sealRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] →
      UnaryHistory L0 →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory E →
              Cont L0 W locatedRead →
                Cont locatedRead R sealRead →
                  UnaryHistory locatedRead ∧ UnaryHistory sealRead ∧
                    Cont L0 W locatedRead ∧ Cont locatedRead R sealRead ∧
                      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist L0)) L0 := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows ledgerUnary windowUnary handoffUnary _sealUnary locatedRoute sealRoute
  cases fieldRows
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed ledgerUnary windowUnary locatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedReadUnary handoffUnary sealRoute
  have ledgerDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist L0)) L0 := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist L0) = L0
    exact LowerRealTasteGate_single_carrier_alignment.1 L0
  exact ⟨locatedReadUnary, sealReadUnary, locatedRoute, sealRoute, ledgerDecode⟩

end BEDC.Derived.LowerRealUp
