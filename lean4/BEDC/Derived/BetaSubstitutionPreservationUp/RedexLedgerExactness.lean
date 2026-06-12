import BEDC.Derived.BetaSubstitutionPreservationUp

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Hist

theorem BetaSubstitutionPreservationRedexLedgerExactness
    {body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
      provenance name : BHist} :
    betaSubstitutionPreservationFromEventFlow
        (betaSubstitutionPreservationToEventFlow
          (BetaSubstitutionPreservationUp.mk body argument redex codomain substitutedBody
            substitutedCodomain ledger transport routes provenance name)) =
      some
        (BetaSubstitutionPreservationUp.mk body argument redex codomain substitutedBody
          substitutedCodomain ledger transport routes provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  change
    some
        (BetaSubstitutionPreservationUp.mk
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist body))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist argument))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist redex))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist codomain))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist substitutedBody))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist substitutedCodomain))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist ledger))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist transport))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist routes))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist provenance))
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist name))) =
      some
        (BetaSubstitutionPreservationUp.mk body argument redex codomain substitutedBody
          substitutedCodomain ledger transport routes provenance name)
  have decodeEncode :
      ∀ h : BHist,
        betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  exact
    congrArg some
      (by
        rw [decodeEncode body, decodeEncode argument, decodeEncode redex,
          decodeEncode codomain, decodeEncode substitutedBody,
          decodeEncode substitutedCodomain, decodeEncode ledger, decodeEncode transport,
          decodeEncode routes, decodeEncode provenance, decodeEncode name])

end BEDC.Derived.BetaSubstitutionPreservationUp
