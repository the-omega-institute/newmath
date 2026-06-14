import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_ledger_route
    {Z S M R Q H C P N sourceRead comparisonRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparisonRead ->
          Cont sourceRead comparisonRead refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row refusalRead ∧ Cont Z S sourceRead ∧
                    Cont M R comparisonRead)
                (fun row : BHist =>
                  hsame row refusalRead ∧ Cont sourceRead comparisonRead refusalRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory sourceRead ∧ UnaryHistory comparisonRead ∧
                  UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont M R comparisonRead ∧
                      Cont sourceRead comparisonRead refusalRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sourceUnary comparisonUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont Z S sourceRead ∧ Cont M R comparisonRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont sourceRead comparisonRead refusalRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact ⟨source.left, sourceRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, sourceUnary, comparisonUnary, refusalUnary,
      sameH, sourceRoute, comparisonRoute, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
