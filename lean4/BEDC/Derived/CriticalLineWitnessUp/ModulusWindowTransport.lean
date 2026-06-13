import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_window_transport
    {Z S M R Q H C P N sourceRead₁ sourceRead₂ modulusRead₁ modulusRead₂ : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead₁ ->
        Cont Z S sourceRead₂ ->
          Cont sourceRead₁ Q modulusRead₁ ->
            Cont sourceRead₂ Q modulusRead₂ ->
              SemanticNameCert
                  (fun row : BHist => hsame row modulusRead₂ ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceRead₁ ∨ hsame row sourceRead₂ ∨ hsame row Q ∨
                      hsame row modulusRead₁ ∨ hsame row modulusRead₂)
                  (fun row : BHist =>
                    hsame row modulusRead₂ ∧ Cont sourceRead₂ Q modulusRead₂)
                  hsame ∧
                UnaryHistory sourceRead₁ ∧ UnaryHistory sourceRead₂ ∧
                  UnaryHistory modulusRead₁ ∧ UnaryHistory modulusRead₂ ∧
                    hsame modulusRead₁ modulusRead₂ ∧
                      Cont sourceRead₂ Q modulusRead₂ := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute₁ sourceRoute₂ modulusRoute₁ modulusRoute₂
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary₁ : UnaryHistory sourceRead₁ :=
    unary_cont_closed unaryZ unaryS sourceRoute₁
  have sourceUnary₂ : UnaryHistory sourceRead₂ :=
    unary_cont_closed unaryZ unaryS sourceRoute₂
  have sourceSame : hsame sourceRead₁ sourceRead₂ :=
    cont_deterministic sourceRoute₁ sourceRoute₂
  have modulusUnary₁ : UnaryHistory modulusRead₁ :=
    unary_cont_closed sourceUnary₁ unaryQ modulusRoute₁
  have modulusUnary₂ : UnaryHistory modulusRead₂ :=
    unary_cont_closed sourceUnary₂ unaryQ modulusRoute₂
  have sameModulus : hsame modulusRead₁ modulusRead₂ :=
    cont_respects_hsame sourceSame (hsame_refl Q) modulusRoute₁ modulusRoute₂
  have sourceAtModulus :
      (fun row : BHist => hsame row modulusRead₂ ∧ UnaryHistory row) modulusRead₂ :=
    ⟨hsame_refl modulusRead₂, modulusUnary₂⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead₂ ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead₁ ∨ hsame row sourceRead₂ ∨ hsame row Q ∨
              hsame row modulusRead₁ ∨ hsame row modulusRead₂)
          (fun row : BHist => hsame row modulusRead₂ ∧ Cont sourceRead₂ Q modulusRead₂)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead₂ sourceAtModulus
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute₂⟩
  }
  exact
    ⟨cert, sourceUnary₁, sourceUnary₂, modulusUnary₁, modulusUnary₂, sameModulus,
      modulusRoute₂⟩

end BEDC.Derived.CriticalLineWitnessUp
