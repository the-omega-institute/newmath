import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_zero_source_refusal
    {Z S M R Q H C P N fixedRead zeroLedger refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedRead ->
        Cont fixedRead Q zeroLedger ->
          Cont zeroLedger N refusalRead ->
            SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row fixedRead ∨ hsame row zeroLedger ∨ hsame row refusalRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Z S fixedRead ∧ Cont fixedRead Q zeroLedger ∧
                  Cont zeroLedger N refusalRead)
              hsame ∧
              UnaryHistory fixedRead ∧ UnaryHistory zeroLedger ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet fixedRoute zeroRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed unaryZ unaryS fixedRoute
  have zeroUnary : UnaryHistory zeroLedger :=
    unary_cont_closed fixedUnary routeClosure.left zeroRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed zeroUnary routeClosure.right.right.left refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row fixedRead ∨ hsame row zeroLedger ∨ hsame row refusalRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Z S fixedRead ∧ Cont fixedRead Q zeroLedger ∧
            Cont zeroLedger N refusalRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, fixedRoute, zeroRoute, refusalRoute⟩
  }
  exact
    ⟨cert, fixedUnary, zeroUnary, refusalUnary, routeClosure.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
