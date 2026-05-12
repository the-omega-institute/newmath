import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MultiHistConfigUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MultiHistConfig_carrier_habitation (h0 h1 : BHist) :
    (Cont h0 BHist.Empty h0 ∧ Cont h1 BHist.Empty h1) ∧
      BEDC.FKernel.NameCert.NameCert
        (fun h : BHist => hsame h h0 ∨ hsame h h1) hsame := by
  constructor
  · constructor
    · exact cont_right_unit h0
    · exact cont_right_unit h1
  · exact {
      carrier_inhabited := Exists.intro h0 (Or.inl (hsame_refl h0))
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro a b c sameAB sameBC
        exact hsame_trans sameAB sameBC
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        cases sameHK
        exact carrierH
    }

end BEDC.Derived.MultiHistConfigUp
