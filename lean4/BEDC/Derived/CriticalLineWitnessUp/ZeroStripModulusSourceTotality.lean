import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_modulus_source_totality
    {Z S M R Q H C P N zeroStrip modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStrip ->
        Cont zeroStrip Q modulusRead ->
          SemanticNameCert
              (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row modulusRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Z S zeroStrip ∧ Cont zeroStrip Q modulusRead)
              hsame ∧ UnaryHistory modulusRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZeroStrip : UnaryHistory zeroStrip :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZeroStrip unaryQ modulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroStrip ∧ Cont zeroStrip Q modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead
        ⟨hsame_refl modulusRead, unaryModulusRead⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zeroStripRoute, modulusRoute⟩
  }
  exact ⟨cert, unaryModulusRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
