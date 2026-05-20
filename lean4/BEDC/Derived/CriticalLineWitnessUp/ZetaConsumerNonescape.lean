import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_consumer_nonescape
    {Z S M R Q H C P N obstructionRead fixedRead zetaRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S obstructionRead →
        Cont obstructionRead N fixedRead →
          Cont fixedRead Q zetaRead →
            Cont zetaRead C consumerRead →
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row consumerRead ∧ Cont Z S obstructionRead ∧
                      Cont obstructionRead N fixedRead)
                  (fun row : BHist =>
                    hsame row consumerRead ∧ Cont zetaRead C consumerRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
                  UnaryHistory N ∧ UnaryHistory obstructionRead ∧ UnaryHistory fixedRead ∧
                    UnaryHistory zetaRead ∧ UnaryHistory consumerRead ∧
                      hsame H (append Z S) ∧ Cont Z S obstructionRead ∧
                        Cont obstructionRead N fixedRead ∧ Cont fixedRead Q zetaRead ∧
                          Cont zetaRead C consumerRead ∧ Cont M R Q ∧ Cont Q H C ∧
                            Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet obstructionRoute fixedRoute zetaRoute consumerRoute
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
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed unaryZ unaryS obstructionRoute
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed obstructionUnary unaryN fixedRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed fixedUnary unaryQ zetaRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed zetaUnary unaryC consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont Z S obstructionRead ∧
              Cont obstructionRead N fixedRead)
          (fun row : BHist => hsame row consumerRead ∧ Cont zetaRead C consumerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, obstructionRoute, fixedRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, consumerRoute⟩
    }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, obstructionUnary, fixedUnary,
      zetaUnary, consumerUnary, sameH, obstructionRoute, fixedRoute, zetaRoute,
      consumerRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_fixed_strip_rh_consumer_boundary
    {Z S M R Q H C P N zeroStripRead modulusRead classifierRead refusalRead rhRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R modulusRead ->
          Cont zeroStripRead modulusRead classifierRead ->
            Cont N Q refusalRead ->
              Cont refusalRead C rhRead ->
                UnaryHistory classifierRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory rhRead ∧ hsame H (append Z S) ∧
                    Cont Z S zeroStripRead ∧ Cont M R Q ∧ Cont M R modulusRead ∧
                      Cont zeroStripRead modulusRead classifierRead ∧
                        Cont N Q refusalRead ∧ Cont refusalRead C rhRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroStripRoute modulusRoute classifierRoute refusalRoute rhRoute
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
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed zeroStripUnary modulusUnary classifierRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryC rhRoute
  exact
    ⟨classifierUnary, refusalUnary, rhUnary, sameH, zeroStripRoute, routeQ, modulusRoute,
      classifierRoute, refusalRoute, rhRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
