import BEDC.Derived.RoundedIntervalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RoundedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def RoundedIntervalRoute (Q S R D L U O E H C P N : BHist) : Prop :=
  UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory O ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont Q S R ∧ Cont R D L ∧ Cont R D U ∧ Cont L U O ∧ Cont O E N

theorem RoundedIntervalDyadicEnclosureStability
    {Q S R D L U O E H C P N replayed : BHist} :
    RoundedIntervalRoute Q S R D L U O E H C P N ->
      Cont O E replayed ->
        SemanticNameCert
            (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row L ∨ hsame row U ∨ hsame row O ∨ hsame row replayed)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Q S R ∧ Cont R D L ∧ Cont R D U ∧
                Cont L U O ∧ Cont O E replayed)
            hsame ∧ UnaryHistory replayed := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro route orderEndpointReplay
  obtain
    ⟨_unaryQ, _unaryS, _unaryR, _unaryD, _unaryL, _unaryU, unaryO, unaryE,
      _unaryH, _unaryC, _unaryP, _unaryN, routeQSR, routeRDL, routeRDU,
      routeLUO, _routeOEN⟩ := route
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed unaryO unaryE orderEndpointReplay
  have sourceReplayed :
      (fun row : BHist => hsame row replayed ∧ UnaryHistory row) replayed := by
    exact ⟨hsame_refl replayed, replayedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row L ∨ hsame row U ∨ hsame row O ∨ hsame row replayed)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q S R ∧ Cont R D L ∧ Cont R D U ∧
              Cont L U O ∧ Cont O E replayed)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayed sourceReplayed
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
      exact
        ⟨source.right, routeQSR, routeRDL, routeRDU, routeLUO,
          orderEndpointReplay⟩
  }
  exact ⟨cert, replayedUnary⟩

end BEDC.Derived.RoundedIntervalUp
