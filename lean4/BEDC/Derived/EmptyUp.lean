import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.EmptyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def EmptyHistoryCarrier (h : BHist) : Prop :=
  hsame h (BHist.e0 BHist.Empty) ∧ hsame h (BHist.e1 BHist.Empty)

theorem EmptyHistoryCarrier_absurd {h : BHist} :
    EmptyHistoryCarrier h -> False := by
  intro carrier
  cases carrier.left
  cases carrier.right

theorem EmptyHistoryCarrier_namecert_absurd :
    NameCert EmptyHistoryCarrier hsame -> False := by
  intro cert
  cases cert.carrier_inhabited with
  | intro _h carrier =>
      exact EmptyHistoryCarrier_absurd carrier

theorem EmptyContradictoryCarrier_namecert_absurd :
    NameCert (fun h : BHist => hsame h BHist.Empty ∧ hsame h (BHist.e1 BHist.Empty))
      hsame -> False := by
  intro cert
  cases cert.carrier_inhabited with
  | intro _h carrier =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.left) carrier.right)

theorem EmptyContradictoryCarrier_semantic_namecert_absurd :
    SemanticNameCert
      (fun h : BHist => hsame h BHist.Empty ∧ hsame h (BHist.e1 BHist.Empty))
      (fun h : BHist => hsame h BHist.Empty ∧ hsame h (BHist.e1 BHist.Empty))
      (fun h : BHist => hsame h BHist.Empty ∧ hsame h (BHist.e1 BHist.Empty))
      hsame -> False := by
  intro cert
  cases semanticNameCert_ledger_policy_witness cert with
  | intro _h carrier =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.left) carrier.right)

theorem EmptyVisibleContradictoryCarrier_namecert_absurd {tail : BHist} :
    NameCert
      (fun h : BHist =>
        hsame h BHist.Empty ∧ (hsame h (BHist.e0 tail) ∨ hsame h (BHist.e1 tail)))
      hsame -> False := by
  intro cert
  cases cert.carrier_inhabited with
  | intro _h carrier =>
      cases carrier.right with
      | inl sameZero =>
          exact not_hsame_emp_e0 (hsame_trans (hsame_symm carrier.left) sameZero)
      | inr sameOne =>
          exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.left) sameOne)

theorem EmptyVisiblePairCarrier_namecert_absurd {left right : BHist} :
    NameCert (fun h : BHist => hsame h (BHist.e0 left) ∧ hsame h (BHist.e1 right))
      hsame -> False := by
  intro cert
  cases cert.carrier_inhabited with
  | intro _h carrier =>
      have mixed : hsame (BHist.e0 left) (BHist.e1 right) :=
        hsame_trans (hsame_symm carrier.left) carrier.right
      exact not_hsame_e0_e1 mixed

theorem EmptyHistoryCarrier_semantic_namecert_absurd :
    SemanticNameCert EmptyHistoryCarrier EmptyHistoryCarrier EmptyHistoryCarrier hsame ->
      False := by
  intro cert
  cases semanticNameCert_ledger_policy_witness cert with
  | intro _h carrier =>
      exact EmptyHistoryCarrier_absurd carrier

theorem EmptyHistoryCarrier_source_semantic_namecert_absurd
    {PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop} :
    SemanticNameCert EmptyHistoryCarrier PatternSpec LedgerPolicy ClassifierSpec -> False := by
  intro cert
  cases cert.core.carrier_inhabited with
  | intro _h carrier =>
      exact EmptyHistoryCarrier_absurd carrier

theorem EmptyVisibleContradictoryCarrier_semantic_namecert_absurd {tail : BHist} :
    SemanticNameCert
      (fun h : BHist =>
        hsame h BHist.Empty ∧ (hsame h (BHist.e0 tail) ∨ hsame h (BHist.e1 tail)))
      (fun h : BHist =>
        hsame h BHist.Empty ∧ (hsame h (BHist.e0 tail) ∨ hsame h (BHist.e1 tail)))
      (fun h : BHist =>
        hsame h BHist.Empty ∧ (hsame h (BHist.e0 tail) ∨ hsame h (BHist.e1 tail)))
      hsame -> False := by
  intro cert
  cases semanticNameCert_ledger_policy_witness cert with
  | intro _h carrier =>
      cases carrier.right with
      | inl sameZero =>
          exact not_hsame_emp_e0 (hsame_trans (hsame_symm carrier.left) sameZero)
      | inr sameOne =>
          exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.left) sameOne)

end BEDC.Derived.EmptyUp
