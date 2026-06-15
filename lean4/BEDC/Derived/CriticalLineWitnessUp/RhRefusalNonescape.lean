import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_nonescape
    {Z S M R Q H C P N refusalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S refusalRead ->
        Cont refusalRead Q rhRead ->
          SemanticNameCert
              (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row rhRead ∧ Cont Z S refusalRead)
              (fun row : BHist => hsame row rhRead ∧ Cont refusalRead Q rhRead)
              hsame ∧
            UnaryHistory refusalRead ∧ UnaryHistory rhRead ∧ hsame H (append Z S) ∧
              Cont Z S refusalRead ∧ Cont refusalRead Q rhRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryZ unaryS refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryQ rhRoute
  have sourceAtRh : hsame rhRead rhRead ∧ UnaryHistory rhRead :=
    ⟨hsame_refl rhRead, rhUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row rhRead ∧ Cont Z S refusalRead)
          (fun row : BHist => hsame row rhRead ∧ Cont refusalRead Q rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead sourceAtRh
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
      exact ⟨source.left, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rhRoute⟩
  }
  exact ⟨cert, refusalUnary, rhUnary, sameH, refusalRoute, rhRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
