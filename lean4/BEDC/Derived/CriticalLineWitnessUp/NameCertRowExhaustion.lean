import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_namecert_row_exhaustion
    {Z S M R Q H C P N nameRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont P N nameRead ->
        SemanticNameCert
            (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row nameRead)
            (fun row : BHist => UnaryHistory row ∧ Cont P N nameRead)
            hsame ∧ UnaryHistory nameRead ∧ Cont P N nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet nameRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, unaryP, _sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryNameRead : UnaryHistory nameRead :=
    unary_cont_closed unaryP routeClosure.right.right.left nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row nameRead)
          (fun row : BHist => UnaryHistory row ∧ Cont P N nameRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, unaryNameRead⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nameRoute⟩
  }
  exact ⟨cert, unaryNameRead, nameRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
