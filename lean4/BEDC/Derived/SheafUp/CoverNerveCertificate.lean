import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

end BEDC.Derived.SheafUp
