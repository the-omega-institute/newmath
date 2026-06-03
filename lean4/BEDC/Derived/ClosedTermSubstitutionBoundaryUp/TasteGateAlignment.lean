import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem ClosedTermSubstitutionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedTermSubstitutionBoundaryDecodeBHist (closedTermSubstitutionBoundaryEncodeBHist h) =
        h) ∧
      (forall x : ClosedTermSubstitutionBoundaryUp,
        closedTermSubstitutionBoundaryFromEventFlow
            (closedTermSubstitutionBoundaryToEventFlow x) =
          some x) ∧
        (forall x y : ClosedTermSubstitutionBoundaryUp,
          closedTermSubstitutionBoundaryToEventFlow x =
              closedTermSubstitutionBoundaryToEventFlow y ->
            x = y) ∧
          closedTermSubstitutionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  obtain ⟨empty_encode, decode_encode, round_trip⟩ :=
    ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment
  constructor
  · exact decode_encode
  · constructor
    · exact round_trip
    · constructor
      · intro x y heq
        have hread :
            closedTermSubstitutionBoundaryFromEventFlow
                (closedTermSubstitutionBoundaryToEventFlow x) =
              closedTermSubstitutionBoundaryFromEventFlow
                (closedTermSubstitutionBoundaryToEventFlow y) :=
          congrArg closedTermSubstitutionBoundaryFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (round_trip x).symm (Eq.trans hread (round_trip y)))
      · exact empty_encode

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp
