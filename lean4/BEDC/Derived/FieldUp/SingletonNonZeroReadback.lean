import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem FieldSingletonNonZero_hsame_target_readback_iff {h k : BHist} :
    hsame h k ->
      (FieldSingletonNonZero h <->
        FieldSingletonCarrier k ∧ hsame k (BHist.e0 BHist.Empty)) := by
  intro sameHK
  constructor
  · intro nonzero
    exact And.intro
      (hsame_trans (hsame_symm sameHK) nonzero.left)
      (hsame_trans (hsame_symm sameHK) nonzero.right)
  · intro data
    exact And.intro
      (hsame_trans sameHK data.left)
      (hsame_trans sameHK data.right)

end BEDC.Derived.FieldUp
