import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootStripSourceTotality {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
          UnaryHistory N ∧ hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
            Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryP, unaryN, sameH,
      routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_strip_source_totality
    {Z S M R Q H C P N sourceRead realRead packageRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R realRead ->
          Cont sourceRead realRead packageRead ->
            SemanticNameCert
                (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row packageRead)
                (fun row : BHist =>
                  hsame row packageRead ∧ Cont sourceRead realRead packageRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory realRead ∧
                  UnaryHistory packageRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont M R realRead ∧
                      Cont sourceRead realRead packageRead ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute realRoute packageRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed sourceUnary realUnary packageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row packageRead)
          (fun row : BHist =>
            hsame row packageRead ∧ Cont sourceRead realRead packageRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead
        ⟨hsame_refl packageRead, packageUnary⟩
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
      exact ⟨source.left, packageRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, realUnary, packageUnary,
      sameH, sourceRoute, realRoute, packageRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
