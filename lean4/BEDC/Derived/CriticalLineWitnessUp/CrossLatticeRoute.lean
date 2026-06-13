import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCrossLatticeRoute
    {Z S M R Q H C P N refusalRead barrierRead counterRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C barrierRead ->
          Cont refusalRead P counterRead ->
            SemanticNameCert
                (fun row : BHist => hsame row barrierRead ∨ hsame row counterRead)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row refusalRead ∨ hsame row barrierRead ∨
                      hsame row counterRead)
                (fun row : BHist =>
                  (hsame row barrierRead ∨ hsame row counterRead) ∧
                    Cont N Q refusalRead ∧ Cont refusalRead C barrierRead ∧
                      Cont refusalRead P counterRead)
                hsame ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory refusalRead ∧ UnaryHistory barrierRead ∧
                  UnaryHistory counterRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute barrierRoute counterRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have unaryP : UnaryHistory P :=
    packet.right.right.right.right.left
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have barrierUnary : UnaryHistory barrierRead :=
    unary_cont_closed refusalUnary routeClosure.right.left barrierRoute
  have counterUnary : UnaryHistory counterRead :=
    unary_cont_closed refusalUnary unaryP counterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row barrierRead ∨ hsame row counterRead)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row refusalRead ∨ hsame row barrierRead ∨
                hsame row counterRead)
          (fun row : BHist =>
            (hsame row barrierRead ∨ hsame row counterRead) ∧
              Cont N Q refusalRead ∧ Cont refusalRead C barrierRead ∧
                Cont refusalRead P counterRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro barrierRead (Or.inl (hsame_refl barrierRead))
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
        cases source with
        | inl sameBarrier =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBarrier)
        | inr sameCounter =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameCounter)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameBarrier =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inl sameBarrier))))))
      | inr sameCounter =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr sameCounter))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, refusalRoute, barrierRoute, counterRoute⟩
  }
  exact
    ⟨cert, routeClosure.left, routeClosure.right.left, routeClosure.right.right.left,
      refusalUnary, barrierUnary, counterUnary, routeClosure.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
