import BEDC.Derived.FanBarRouteUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FanBarRouteUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FanBarRouteFiniteBarHandoff (x : FanBarRouteUp)
    {T B I W Q D E H C P N readB readI readW readQ readD readE : BHist} :
    x = FanBarRouteUp.mk T B I W Q D E H C P N ->
      Cont T B readB ->
        Cont readB I readI ->
          Cont readI W readW ->
            Cont readW Q readQ ->
              Cont readQ D readD ->
                Cont readD E readE ->
                  UnaryHistory T ->
                    UnaryHistory B ->
                      UnaryHistory I ->
                        UnaryHistory W ->
                          UnaryHistory Q ->
                            UnaryHistory D ->
                              UnaryHistory E ->
                                UnaryHistory readB ∧ UnaryHistory readI ∧
                                  UnaryHistory readW ∧ UnaryHistory readQ ∧
                                    UnaryHistory readD ∧ UnaryHistory readE ∧
                                      Cont T B readB ∧ Cont readB I readI ∧
                                        Cont readI W readW ∧ Cont readW Q readQ ∧
                                          Cont readQ D readD ∧ Cont readD E readE := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro _carrierEq routeB routeI routeW routeQ routeD routeE unaryT unaryB unaryI unaryW
    unaryQ unaryD _unaryE
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed unaryT unaryB routeB
  have readIUnary : UnaryHistory readI :=
    unary_cont_closed readBUnary unaryI routeI
  have readWUnary : UnaryHistory readW :=
    unary_cont_closed readIUnary unaryW routeW
  have readQUnary : UnaryHistory readQ :=
    unary_cont_closed readWUnary unaryQ routeQ
  have readDUnary : UnaryHistory readD :=
    unary_cont_closed readQUnary unaryD routeD
  have readEUnary : UnaryHistory readE :=
    unary_cont_closed readDUnary _unaryE routeE
  exact
    ⟨readBUnary, readIUnary, readWUnary, readQUnary, readDUnary, readEUnary, routeB,
      routeI, routeW, routeQ, routeD, routeE⟩

end BEDC.Derived.FanBarRouteUp
