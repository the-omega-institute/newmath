import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCompletionHandoffExactness
    {P S M C W R E T K G N sourceRead completionRead handoffRead nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S sourceRead →
        Cont M C completionRead →
          Cont sourceRead completionRead handoffRead →
            Cont G N nameRead →
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                        hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row sourceRead ∨
                          hsame row completionRead ∨ hsame row handoffRead ∨
                            hsame row nameRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                      Cont P S sourceRead ∧ Cont M C completionRead ∧
                        Cont sourceRead completionRead handoffRead ∧ Cont G N nameRead)
                  hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory completionRead ∧
                UnaryHistory handoffRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData sourceRoute completionRoute handoffRoute nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, gUnary, nUnary, _sourceCarrierRoute, _completionCarrierRoute⟩ := carrierData
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed pUnary sUnary sourceRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sourceUnary completionUnary handoffRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row completionRead ∨
                  hsame row handoffRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S sourceRead ∧ Cont M C completionRead ∧
                Cont sourceRead completionRead handoffRead ∧ Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, sourceRoute, completionRoute, handoffRoute,
          nameRoute⟩
  }
  exact ⟨cert, sourceUnary, completionUnary, handoffUnary, nameUnary⟩

end BEDC.Derived.HausdorffizationUp
