import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationNonquotientNonescapeObligation
    {P S M C W R E T K G N separatedRead completionRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N ->
      Cont P S separatedRead ->
        Cont M C completionRead ->
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                  hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                    hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row completionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                  Cont P S separatedRead ∧ Cont M C completionRead)
              hsame ∧
            UnaryHistory separatedRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData separatedRoute completionRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed pUnary sUnary separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S separatedRead ∧ Cont M C completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, separatedRoute, completionRoute⟩
  }
  exact ⟨cert, separatedUnary, completionUnary⟩

end BEDC.Derived.HausdorffizationUp
