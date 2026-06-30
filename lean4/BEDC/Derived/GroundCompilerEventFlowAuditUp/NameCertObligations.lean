import BEDC.Derived.GroundCompilerEventFlowAuditUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.GroundCompilerEventFlowAuditUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def GroundCompilerEventFlowAuditCarrier
    (S F C L R G A H K P N : BHist) : Prop :=
  UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory C ∧ UnaryHistory L ∧
    UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory H ∧
      UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory N

theorem GroundCompilerEventFlowAuditCarrier_namecert_obligations
    {S F C L R G A H K P N sourceRead channelRead recognizerRead gateRead : BHist} :
    GroundCompilerEventFlowAuditCarrier S F C L R G A H K P N ->
      Cont S F sourceRead ->
        Cont C L channelRead ->
          Cont G A recognizerRead ->
            Cont channelRead recognizerRead gateRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row F ∨ hsame row C ∨ hsame row L ∨
                      hsame row G ∨ hsame row A ∨ hsame row gateRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont channelRead recognizerRead gateRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory channelRead ∧
                  UnaryHistory recognizerRead ∧ UnaryHistory gateRead := by
  -- BEDC touchpoint anchor: GroundCompilerEventFlowAuditCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute channelRoute recognizerRoute gateRoute
  obtain ⟨sUnary, fUnary, cUnary, lUnary, _rUnary, gUnary, aUnary, _hUnary, _kUnary,
    _pUnary, _nUnary⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary fUnary sourceRoute
  have channelUnary : UnaryHistory channelRead :=
    unary_cont_closed cUnary lUnary channelRoute
  have recognizerUnary : UnaryHistory recognizerRead :=
    unary_cont_closed gUnary aUnary recognizerRoute
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed channelUnary recognizerUnary gateRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row F ∨ hsame row C ∨ hsame row L ∨
              hsame row G ∨ hsame row A ∨ hsame row gateRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont channelRead recognizerRead gateRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gateRead ⟨hsame_refl gateRead, gateUnary⟩
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
      exact ⟨source.right, gateRoute⟩
  }
  exact ⟨cert, sourceUnary, channelUnary, recognizerUnary, gateUnary⟩

end BEDC.Derived.GroundCompilerEventFlowAuditUp
