import BEDC.Derived.RegularCauchyMinimumUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinimumUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyMinimumLeftBound
    {X Y T L D A B W H C P N requestRead branchRead outputRead : BHist} :
    UnaryHistory X ->
      UnaryHistory T ->
        UnaryHistory L ->
          UnaryHistory W ->
            Cont X T requestRead ->
              Cont requestRead L branchRead ->
                Cont branchRead W outputRead ->
                  regularCauchyMinimumFromEventFlow
                      (regularCauchyMinimumToEventFlow
                        (RegularCauchyMinimumUp.mk X Y T L D A B W H C P N)) =
                    some (RegularCauchyMinimumUp.mk X Y T L D A B W H C P N) ->
                    UnaryHistory requestRead ∧
                      UnaryHistory branchRead ∧
                        UnaryHistory outputRead ∧
                          hsame
                            (regularCauchyMinimumDecodeBHist
                              (regularCauchyMinimumEncodeBHist W))
                            W := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro xUnary toleranceUnary locatedUnary windowUnary requestRoute branchRoute outputRoute
    roundTrip
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary toleranceUnary requestRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed requestUnary locatedUnary branchRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary windowUnary outputRoute
  have windowDecode :
      hsame
        (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist W))
        W := by
    change regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist W) = W
    exact RegularCauchyMinimumTasteGate_single_carrier_alignment.1 W
  exact ⟨requestUnary, branchUnary, outputUnary, windowDecode⟩

end BEDC.Derived.RegularCauchyMinimumUp
