import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

theorem add_up_license_with_shift_and_commutativity {h k r r' : BHist}
    (uh : UnaryHistory h) (uk : UnaryHistory k) (hr : Cont h k r) (hr' : Cont k h r') :
    NameCert UnaryHistory AddClassifierSpec ∧ hsame r r' := by
  constructor
  · exact add_up_name_certificate
  · exact unary_cont_comm uh uk hr hr'

theorem upgrade_additive_naming_certificate_with_ledger {h k r r' : BHist}
    (uh : UnaryHistory h) (uk : UnaryHistory k) (hr : Cont h k r) (hr' : Cont k h r') :
    NameCert UnaryHistory AddClassifierSpec /\ hsame r r' := by
  constructor
  · exact add_up_name_certificate
  · exact unary_cont_comm uh uk hr hr'

theorem upgrade_additive_naming_certificate {h k r rprime : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h rprime ->
      NameCert UnaryHistory AddClassifierSpec /\ hsame r rprime := by
  intro uh uk hr hrprime
  constructor
  · exact add_up_name_certificate
  · exact unary_cont_comm uh uk hr hrprime

theorem additive_certificate_upgrade {h k r rprime : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h rprime ->
      NameCert UnaryHistory AddClassifierSpec /\ hsame r rprime := by
  intro uh uk hr hrprime
  constructor
  · exact add_up_name_certificate
  · exact unary_cont_comm uh uk hr hrprime

end BEDC.FKernel.Unary
