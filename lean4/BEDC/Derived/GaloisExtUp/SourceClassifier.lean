import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Sig

def GaloisExtSourceClassifier [AskSetup]
    (bundle : ProbeBundle ProbeName)
    (field separable normal automorphism classifier provenance ledger field' separable' normal'
      automorphism' classifier' provenance' ledger' : BHist) : Prop :=
  SameSig bundle field field' ∧ SameSig bundle separable separable' ∧
    SameSig bundle normal normal' ∧ SameSig bundle automorphism automorphism' ∧
      SameSig bundle classifier classifier' ∧ hsame provenance provenance' ∧ hsame ledger ledger'

end BEDC.Derived.GaloisExtUp
