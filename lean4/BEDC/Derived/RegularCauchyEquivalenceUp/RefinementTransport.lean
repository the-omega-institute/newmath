import BEDC.Derived.RegularCauchyEquivalenceUp.TasteGate

namespace BEDC.Derived.RegularCauchyEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RegularCauchyEquivalence_refinement_transport
    {X Y W D Z R E H C P N X' Y' W' D' Z' R' E' H' C' P' N' : BHist}
    (hX : hsame X X') (hY : hsame Y Y') (hW : hsame W W') (hD : hsame D D')
    (hZ : hsame Z Z') (hR : hsame R R') (hE : hsame E E') (hH : hsame H H')
    (hC : hsame C C') (hP : hsame P P') (hN : hsame N N') :
    regularCauchyEquivalenceFromEventFlow
        (regularCauchyEquivalenceToEventFlow
          (RegularCauchyEquivalenceUp.mk X' Y' W' D' Z' R' E' H' C' P' N')) =
          some (RegularCauchyEquivalenceUp.mk X' Y' W' D' Z' R' E' H' C' P' N') ∧
      regularCauchyEquivalenceFields
          (RegularCauchyEquivalenceUp.mk X' Y' W' D' Z' R' E' H' C' P' N') =
        [X', Y', W', D', Z', R', E', H', C', P', N'] ∧
      regularCauchyEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases hX
  cases hY
  cases hW
  cases hD
  cases hZ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  exact
    ⟨(RegularCauchyEquivalenceTasteGate_single_carrier_alignment).right.left
        (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N),
      rfl,
      rfl⟩

end BEDC.Derived.RegularCauchyEquivalenceUp
