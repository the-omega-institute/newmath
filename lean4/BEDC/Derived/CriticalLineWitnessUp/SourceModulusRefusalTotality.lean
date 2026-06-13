import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_refusal_totality
    {Z S M R Q H C P N sourceRead modulusRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q modulusRead ->
          Cont N Q downstream ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                UnaryHistory downstream ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                  Cont sourceRead Q modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N ∧ Cont N Q downstream := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet sourceRoute modulusRoute downstreamRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unarySourceRead routeClosure.left modulusRoute
  have unaryDownstream : UnaryHistory downstream :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left downstreamRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unarySourceRead,
      unaryModulusRead, unaryDownstream, sameH, sourceRoute, modulusRoute, routeQ, routeC,
      routeN, downstreamRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
