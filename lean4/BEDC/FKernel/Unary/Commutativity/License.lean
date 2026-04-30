import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

local instance : NameCertSetup := MinimalNameCertSetup

theorem add_up_license_with_shift_and_commutativity {h k r r' : BHist}
    (uh : UnaryHistory h) (uk : UnaryHistory k) (hr : Cont h k r) (hr' : Cont k h r') :
    NameCert AddName ∧ hsame r r' ∧ Nonempty LedgerPolicy := by
  constructor
  · exact add_up_name_certificate
  · constructor
    · exact unary_cont_comm uh uk hr hr'
    · exact add_up_certificate_has_ledger

end BEDC.FKernel.Unary
