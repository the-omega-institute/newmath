import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_consumer_boundary
    {Z S M R Q H C P N stripRead modulusRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S stripRead →
        Cont stripRead Q modulusRead →
          Cont modulusRead N consumerRead →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row consumerRead ∧ Cont Z S stripRead ∧
                    Cont stripRead Q modulusRead)
                (fun row : BHist =>
                  hsame row consumerRead ∧ Cont modulusRead N consumerRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                  UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory consumerRead ∧ hsame H (append Z S) ∧
                      Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                        Cont modulusRead N consumerRead ∧ Cont M R Q ∧ Cont Q H C ∧
                          Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute consumerRoute
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
  have unaryStripRead : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryStripRead unaryQ modulusRoute
  have unaryConsumerRead : UnaryHistory consumerRead :=
    unary_cont_closed unaryModulusRead unaryN consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, unaryConsumerRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont Z S stripRead ∧ Cont stripRead Q modulusRead)
          (fun row : BHist => hsame row consumerRead ∧ Cont modulusRead N consumerRead)
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
      exact ⟨source.left, stripRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, unaryStripRead,
      unaryModulusRead, unaryConsumerRead, sameH, stripRoute, modulusRoute,
      consumerRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
