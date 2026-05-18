import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryDepthRowStability
    {source value depth shift substitution shift' substitution' : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      hsame shift shift' ->
        Cont shift' depth substitution' ->
          UnaryHistory depth ∧ UnaryHistory shift' ∧ UnaryHistory substitution' ∧
            hsame substitution substitution' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier sameShift shiftDepthSubstitution'
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, _substitutionUnary,
    _sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have shiftUnary' : UnaryHistory shift' :=
    unary_transport shiftUnary sameShift
  have substitutionUnary' : UnaryHistory substitution' :=
    unary_cont_closed shiftUnary' depthUnary shiftDepthSubstitution'
  have sameSubstitution : hsame substitution substitution' :=
    cont_respects_hsame sameShift (hsame_refl depth) shiftDepthSubstitution
      shiftDepthSubstitution'
  exact ⟨depthUnary, shiftUnary', substitutionUnary', sameSubstitution⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
