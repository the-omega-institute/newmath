import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_ledger_exhaustion
    {Z S M R Q H C P N modulusRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q downstreamRead ->
          SemanticNameCert
              (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row downstreamRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M R modulusRead ∧
                  Cont modulusRead Q downstreamRead)
              hsame ∧
            UnaryHistory modulusRead ∧ UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute downstreamRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed modulusUnary unaryQ downstreamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row downstreamRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R modulusRead ∧ Cont modulusRead Q downstreamRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro downstreamRead ⟨hsame_refl downstreamRead, downstreamUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusRoute, downstreamRoute⟩
  }
  exact ⟨cert, modulusUnary, downstreamUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
