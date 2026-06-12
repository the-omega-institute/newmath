import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_window_totality
    {Z S M R Q H C P N rootWindow : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R rootWindow →
        SemanticNameCert
            (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row rootWindow)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont M R rootWindow ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N)
            hsame ∧ UnaryHistory rootWindow ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusRootWindow
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed unaryM unaryR modulusRootWindow
  have sourceRootWindow :
      (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row) rootWindow := by
    exact ⟨hsame_refl rootWindow, rootWindowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row rootWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R rootWindow ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootWindow sourceRootWindow
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusRootWindow, routeQ, routeC, routeN⟩
  }
  exact ⟨cert, rootWindowUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
