import BEDC.Derived.LowerRealUp.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LowerRealPublicPackage_scope
    {L0 W R E H C P N locatedRead sealRead publicRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont L0 W locatedRead ->
                Cont locatedRead R sealRead ->
                  Cont sealRead E publicRead ->
                    UnaryHistory locatedRead ∧
                      UnaryHistory sealRead ∧
                        UnaryHistory publicRead ∧
                          hsame (lowerRealDecodeBHist (lowerRealEncodeBHist N)) N := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows l0Unary windowUnary regularUnary sealUnary locatedRoute sealRoute publicRoute
  cases fieldRows
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed l0Unary windowUnary locatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedUnary regularUnary sealRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary sealUnary publicRoute
  have nameDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist N)) N := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist N) = N
    exact LowerRealTasteGate_single_carrier_alignment.1 N
  exact ⟨locatedUnary, sealReadUnary, publicReadUnary, nameDecode⟩

end BEDC.Derived.LowerRealUp
