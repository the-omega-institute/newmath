import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ContinuationMonadCarrier_route_readback_determinacy
    {A B C f g u H K L N unitRead unitRead' firstRead firstRead' secondRead secondRead'
      compositeRead compositeRead' : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u N unitRead ->
        Cont u N unitRead' ->
          Cont A f firstRead ->
            Cont A f firstRead' ->
              Cont B g secondRead ->
                Cont B g secondRead' ->
                  Cont K L compositeRead ->
                    Cont K L compositeRead' ->
                      hsame unitRead unitRead' ∧ hsame firstRead firstRead' ∧
                        hsame secondRead secondRead' ∧
                          hsame compositeRead compositeRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _carrier unitRoute unitRoute' firstRoute firstRoute' secondRoute secondRoute'
    compositeRoute compositeRoute'
  exact
    ⟨cont_deterministic unitRoute unitRoute',
      cont_deterministic firstRoute firstRoute',
      cont_deterministic secondRoute secondRoute',
      cont_deterministic compositeRoute compositeRoute'⟩

end BEDC.Derived.ContinuationMonadUp
