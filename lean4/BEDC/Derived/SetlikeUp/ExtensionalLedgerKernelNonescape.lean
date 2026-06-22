import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeExtensionalLedgerKernelNonescape [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N extensionalRead namedRead : BHist} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory N ->
                  Cont M Q extensionalRead ->
                    Cont extensionalRead N namedRead ->
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
                              hsame row E ∨ hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M Q extensionalRead ∧
                              Cont extensionalRead N namedRead)
                          hsame ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont SemanticNameCert hsame UnaryHistory
  intro fields mUnary qUnary _iUnary _rUnary _eUnary nUnary extensionalRoute namedRoute
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed mUnary qUnary extensionalRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed extensionalUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q extensionalRead ∧ Cont extensionalRead N namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, extensionalRoute, namedRoute⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
