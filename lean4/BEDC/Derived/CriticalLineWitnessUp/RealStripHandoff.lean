import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_real_strip_handoff
    {Z S M R Q H C P N realStripRead handoffRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont S R realStripRead ->
        Cont realStripRead Q handoffRead ->
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row R ∨ hsame row Q ∨ hsame row M ∨
                  hsame row realStripRead ∨ hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont S R realStripRead ∧
                  Cont realStripRead Q handoffRead)
              hsame ∧
            UnaryHistory realStripRead ∧ UnaryHistory handoffRead ∧ Cont M R Q := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet realStripRoute handoffRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryRealStrip : UnaryHistory realStripRead :=
    unary_cont_closed _unaryS unaryR realStripRoute
  have unaryHandoff : UnaryHistory handoffRead :=
    unary_cont_closed unaryRealStrip unaryQ handoffRoute
  have sourceAtHandoff : hsame handoffRead handoffRead ∧ UnaryHistory handoffRead :=
    ⟨hsame_refl handoffRead, unaryHandoff⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row Q ∨ hsame row M ∨
              hsame row realStripRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R realStripRead ∧
              Cont realStripRead Q handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceAtHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realStripRoute, handoffRoute⟩
  }
  exact ⟨cert, unaryRealStrip, unaryHandoff, routeQ⟩

end BEDC.Derived.CriticalLineWitnessUp
