import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zeta_ledger_nonescape
    {Z S M R Q H C P N zetaRead continuationRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q continuationRead ->
          Cont continuationRead N downstreamRead ->
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont Z S zetaRead ∧
                    Cont zetaRead Q continuationRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont continuationRead N downstreamRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory continuationRead ∧
                  UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                    Cont zetaRead Q continuationRead ∧
                      Cont continuationRead N downstreamRead ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute continuationRoute downstreamRoute
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
  have sameHOut : hsame H (append Z S) :=
    sameH
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed zetaUnary unaryQ continuationRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed continuationUnary unaryN downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont Z S zetaRead ∧
              Cont zetaRead Q continuationRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont continuationRead N downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceAtDownstream
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
      exact ⟨source.left, zetaRoute, continuationRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, zetaUnary, continuationUnary, downstreamUnary,
      sameHOut, zetaRoute, continuationRoute, downstreamRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
