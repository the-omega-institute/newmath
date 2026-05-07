import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafBHistCoverNerveLedger_semantic_name_certificate
    {ambient member overlap route germ : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistCoverNerveLedger ambient member overlap route endpoint)
        (fun endpoint : BHist => SheafBHistCoverNerveLedger ambient member overlap route endpoint)
        (fun endpoint : BHist => SheafBHistCoverNerveLedger ambient member overlap route endpoint)
        hsame := by
  intro ledger
  constructor
  · constructor
    · exact Exists.intro germ ledger
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (cont_result_hsame_transport carrier.right.right.right.right same))))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

theorem SheafRootCoverNerve_exact_globalize_package
    {ambient member overlap route germ nextRoute nextGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      UnaryHistory nextRoute -> Cont member nextRoute nextGerm ->
        SemanticNameCert
            (fun endpoint : BHist =>
              SheafBHistCoverNerveLedger ambient member member nextRoute endpoint)
            (fun endpoint : BHist =>
              SheafBHistPointGermLedger ambient member nextRoute endpoint)
            (fun endpoint : BHist =>
              SheafBHistCoverNerveLedger ambient member member nextRoute endpoint)
            hsame ∧
          SheafBHistPointGermLedger ambient member nextRoute nextGerm ∧
            UnaryHistory nextGerm := by
  intro ledger nextRouteUnary nextRow
  have membership :
      SheafBHistCoverNerveLedger ambient member member nextRoute nextGerm ∧
        UnaryHistory nextGerm :=
    SheafRootCoverNerve_membership_exhaustion ledger nextRouteUnary nextRow
  have pointLedger : SheafBHistPointGermLedger ambient member nextRoute nextGerm :=
    And.intro ledger.left (And.intro ledger.right.left nextRow)
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistCoverNerveLedger ambient member member nextRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member nextRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistCoverNerveLedger ambient member member nextRoute endpoint)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro nextGerm membership.left
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro endpoint endpoint' same
        exact hsame_symm same
      · intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        exact And.intro carrier.left
          (And.intro carrier.right.left
            (And.intro carrier.right.right.left
              (And.intro carrier.right.right.right.left
                (cont_result_hsame_transport carrier.right.right.right.right same))))
    · intro endpoint source
      exact And.intro source.left
        (And.intro source.right.left source.right.right.right.right)
    · intro _endpoint source
      exact source
  exact And.intro cert (And.intro pointLedger membership.right)

end BEDC.Derived.SheafUp
