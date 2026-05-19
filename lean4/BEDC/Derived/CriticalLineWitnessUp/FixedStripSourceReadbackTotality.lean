import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_source_readback_totality
    {Z S M R Q H C P N sourceRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q modulusRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row modulusRead)
                (fun row : BHist => hsame row modulusRead ∧ Cont sourceRead Q modulusRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont sourceRead Q modulusRead ∧
                      Cont N Q refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryQ modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtModulus : hsame modulusRead modulusRead ∧ UnaryHistory modulusRead :=
    ⟨hsame_refl modulusRead, modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row modulusRead)
          (fun row : BHist => hsame row modulusRead ∧ Cont sourceRead Q modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
      exact ⟨source.left, modulusRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, modulusUnary,
      refusalUnary, sameH, sourceRoute, modulusRoute, refusalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
