import BEDC.FKernel.NameCert

namespace BEDC.Derived.EmptyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem EmptyContradictoryCarrier_namecert_absurd :
    NameCert (fun h : BHist => hsame h BHist.Empty ∧ hsame h (BHist.e1 BHist.Empty))
      hsame -> False := by
  intro cert
  cases cert.carrier_inhabited with
  | intro _h carrier =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.left) carrier.right)

end BEDC.Derived.EmptyUp
