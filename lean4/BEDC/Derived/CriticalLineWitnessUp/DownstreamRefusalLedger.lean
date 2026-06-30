import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_refusal_ledger
    {Z S M R Q H C P N refusalRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C downstreamRead ->
          SemanticNameCert
              (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                  hsame row refusalRead ∨ hsame row downstreamRead)
              (fun row : BHist =>
                hsame row downstreamRead ∧ Cont N Q refusalRead ∧
                  Cont refusalRead C downstreamRead)
              hsame ∧
            UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute downstreamRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed refusalUnary routeClosure.right.left downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row refusalRead ∨ hsame row downstreamRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont N Q refusalRead ∧
              Cont refusalRead C downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceAtDownstream
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, downstreamRoute⟩
  }
  exact ⟨cert, downstreamUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
