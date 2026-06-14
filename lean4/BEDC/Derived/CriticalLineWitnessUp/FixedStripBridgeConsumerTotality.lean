import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessFixedStripBridgeConsumerTotality
    {Z S M R Q H C P N bridgeRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S bridgeRead ->
        Cont bridgeRead N consumerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Z S bridgeRead ∧ Cont bridgeRead N consumerRead)
              hsame ∧
            UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet bridgeRoute consumerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryBridgeRead : UnaryHistory bridgeRead :=
    unary_cont_closed unaryZ unaryS bridgeRoute
  have unaryConsumerRead : UnaryHistory consumerRead :=
    unary_cont_closed unaryBridgeRead routeClosure.right.right.left consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, unaryConsumerRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S bridgeRead ∧ Cont bridgeRead N consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, consumerRoute⟩
  }
  exact ⟨cert, unaryConsumerRead⟩

theorem CriticalLineWitnessCarrier_fixed_strip_bridge_consumer_totality
    {Z S M R Q H C P N imageRead readbackRead bridgeRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S imageRead ->
        Cont imageRead Q readbackRead ->
          Cont readbackRead N bridgeRead ->
            Cont N Q refusalRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row bridgeRead ∧ Cont Z S imageRead ∧
                      Cont imageRead Q readbackRead)
                  (fun row : BHist =>
                    hsame row bridgeRead ∧ Cont readbackRead N bridgeRead ∧
                      Cont N Q refusalRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory imageRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory bridgeRead ∧ UnaryHistory refusalRead ∧
                        hsame H (append Z S) ∧ Cont Z S imageRead ∧
                          Cont imageRead Q readbackRead ∧
                            Cont readbackRead N bridgeRead ∧ Cont N Q refusalRead ∧
                              Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet imageRoute readbackRoute bridgeRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed unaryZ unaryS imageRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed imageUnary unaryQ readbackRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed readbackUnary unaryN bridgeRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtBridge : hsame bridgeRead bridgeRead ∧ UnaryHistory bridgeRead :=
    ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bridgeRead ∧ Cont Z S imageRead ∧ Cont imageRead Q readbackRead)
          (fun row : BHist =>
            hsame row bridgeRead ∧ Cont readbackRead N bridgeRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
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
      exact ⟨source.left, imageRoute, readbackRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgeRoute, refusalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, imageUnary,
      readbackUnary, bridgeUnary, refusalUnary, sameH, imageRoute, readbackRoute,
      bridgeRoute, refusalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
