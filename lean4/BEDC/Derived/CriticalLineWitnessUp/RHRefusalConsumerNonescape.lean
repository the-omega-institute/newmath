import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_consumer_nonescape
    {Z S M R Q H C P N fixedStrip refusalRead rhConsumer : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedStrip ->
        Cont N Q refusalRead ->
          Cont refusalRead C rhConsumer ->
            SemanticNameCert
                (fun row : BHist => hsame row rhConsumer ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row rhConsumer ∧ Cont Z S fixedStrip ∧ Cont N Q refusalRead)
                (fun row : BHist =>
                  hsame row rhConsumer ∧ Cont refusalRead C rhConsumer)
                hsame ∧
              UnaryHistory fixedStrip ∧ UnaryHistory refusalRead ∧ UnaryHistory rhConsumer ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet fixedRoute refusalRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryFixed : UnaryHistory fixedStrip :=
    unary_cont_closed unaryZ unaryS fixedRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryConsumer : UnaryHistory rhConsumer :=
    unary_cont_closed unaryRefusal unaryC consumerRoute
  have sourceAtConsumer : hsame rhConsumer rhConsumer ∧ UnaryHistory rhConsumer :=
    ⟨hsame_refl rhConsumer, unaryConsumer⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhConsumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rhConsumer ∧ Cont Z S fixedStrip ∧ Cont N Q refusalRead)
          (fun row : BHist =>
            hsame row rhConsumer ∧ Cont refusalRead C rhConsumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhConsumer sourceAtConsumer
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
      exact ⟨source.left, fixedRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact ⟨cert, unaryFixed, unaryRefusal, unaryConsumer, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
