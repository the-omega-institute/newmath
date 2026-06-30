import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_budget_public_interface
    {Z S M R Q H C P N sourceRead refusalRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont N Q refusalRead ->
          Cont sourceRead refusalRead publicRead ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row publicRead)
                (fun row : BHist =>
                  hsame row publicRead ∧ Cont sourceRead refusalRead publicRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
                UnaryHistory sourceRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory publicRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont N Q refusalRead ∧
                      Cont sourceRead refusalRead publicRead ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute refusalRoute publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary refusalUnary publicRoute
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont sourceRead refusalRead publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, sourceUnary, refusalUnary, publicUnary, sameH,
      sourceRoute, refusalRoute, publicRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
