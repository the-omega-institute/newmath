import BEDC.Derived.DigestFiberLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DigestFiberLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DigestFiberLedgerNonEscape
    {visible fiber gap refusal transport continuation provenance name digestRead : BHist} :
    Cont visible fiber digestRead →
      UnaryHistory visible →
        UnaryHistory fiber →
          UnaryHistory gap →
            UnaryHistory refusal →
              UnaryHistory transport →
                UnaryHistory continuation →
                  UnaryHistory provenance →
                    UnaryHistory name →
                      SemanticNameCert
                          (fun row : BHist => hsame row digestRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row visible ∨ hsame row fiber ∨ hsame row gap ∨
                              hsame row refusal ∨ hsame row transport ∨
                                hsame row continuation ∨ hsame row provenance ∨
                                  hsame row name ∨ hsame row digestRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont visible fiber digestRead)
                          hsame ∧
                        UnaryHistory digestRead := by
  -- BEDC touchpoint anchor: DigestFiberLedgerUp BHist Cont SemanticNameCert hsame UnaryHistory
  intro digestRoute visibleUnary fiberUnary _gapUnary _refusalUnary _transportUnary
    _continuationUnary _provenanceUnary _nameUnary
  have digestUnary : UnaryHistory digestRead :=
    unary_cont_closed visibleUnary fiberUnary digestRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row digestRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row visible ∨ hsame row fiber ∨ hsame row gap ∨ hsame row refusal ∨
              hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
                hsame row name ∨ hsame row digestRead)
          (fun row : BHist => UnaryHistory row ∧ Cont visible fiber digestRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro digestRead ⟨hsame_refl digestRead, digestUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, digestRoute⟩
  }
  exact ⟨cert, digestUnary⟩

end BEDC.Derived.DigestFiberLedgerUp
