import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Derived.MetricTopologyUp.TasteGate

namespace BEDC.Derived.MetricTopologyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricTopologyCarrier_ball_basis_scope
    {M B T R Q H C P N ballOpen topologyOpen publicOpen : BHist} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory T ->
          UnaryHistory R ->
            UnaryHistory Q ->
              Cont M B ballOpen ->
                Cont ballOpen T topologyOpen ->
                  Cont topologyOpen R publicOpen ->
                    hsame publicOpen N ->
                      UnaryHistory ballOpen ∧ UnaryHistory topologyOpen ∧
                        UnaryHistory publicOpen ∧ Cont M B ballOpen ∧
                          Cont ballOpen T topologyOpen ∧ Cont topologyOpen R publicOpen ∧
                            hsame publicOpen N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro mUnary bUnary tUnary rUnary _qUnary ballCont topologyCont publicCont publicSame
  have ballUnary : UnaryHistory ballOpen :=
    unary_cont_closed mUnary bUnary ballCont
  have topologyUnary : UnaryHistory topologyOpen :=
    unary_cont_closed ballUnary tUnary topologyCont
  have publicUnary : UnaryHistory publicOpen :=
    unary_cont_closed topologyUnary rUnary publicCont
  exact
    ⟨ballUnary, topologyUnary, publicUnary, ballCont, topologyCont, publicCont, publicSame⟩

theorem MetricTopologyCarrier_namecert_obligations
    {M B T R Q H C P N ballOpen topologyOpen publicOpen : BHist} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory T ->
          UnaryHistory R ->
            UnaryHistory Q ->
              Cont M B ballOpen ->
                Cont ballOpen T topologyOpen ->
                  Cont topologyOpen R publicOpen ->
                    hsame publicOpen N ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicOpen ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row B ∨ hsame row T ∨ hsame row R ∨
                              hsame row Q ∨ hsame row publicOpen)
                          (fun row : BHist => hsame row publicOpen ∧ hsame publicOpen N)
                          hsame ∧
                        UnaryHistory ballOpen ∧ UnaryHistory topologyOpen ∧
                          UnaryHistory publicOpen ∧ Cont M B ballOpen ∧
                            Cont ballOpen T topologyOpen ∧ Cont topologyOpen R publicOpen ∧
                              hsame publicOpen N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro mUnary bUnary tUnary rUnary _qUnary ballCont topologyCont publicCont publicSame
  have ballUnary : UnaryHistory ballOpen :=
    unary_cont_closed mUnary bUnary ballCont
  have topologyUnary : UnaryHistory topologyOpen :=
    unary_cont_closed ballUnary tUnary topologyCont
  have publicUnary : UnaryHistory publicOpen :=
    unary_cont_closed topologyUnary rUnary publicCont
  have publicSource : hsame publicOpen publicOpen ∧ UnaryHistory publicOpen :=
    ⟨hsame_refl publicOpen, publicUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicOpen ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row B ∨ hsame row T ∨ hsame row R ∨ hsame row Q ∨
            hsame row publicOpen)
        (fun row : BHist => hsame row publicOpen ∧ hsame publicOpen N)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicOpen publicSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicSame⟩
  }
  exact
    ⟨cert, ballUnary, topologyUnary, publicUnary, ballCont, topologyCont, publicCont,
      publicSame⟩

end BEDC.Derived.MetricTopologyUp
