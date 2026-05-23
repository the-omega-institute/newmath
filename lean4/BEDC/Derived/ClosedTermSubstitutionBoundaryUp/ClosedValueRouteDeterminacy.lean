import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosedValueRouteDeterminacy [AskSetup] [PackageSetup]
    {source value depth shift substitution valueReadA valueReadB substitutionReadA
      substitutionReadB : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont value depth valueReadA ->
        Cont value depth valueReadB ->
          Cont shift valueReadA substitutionReadA ->
            Cont shift valueReadB substitutionReadB ->
              hsame valueReadA valueReadB ∧ hsame substitutionReadA substitutionReadB ∧
                UnaryHistory valueReadA ∧ UnaryHistory valueReadB ∧
                  UnaryHistory substitutionReadA ∧ UnaryHistory substitutionReadB := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier valueDepthReadA valueDepthReadB shiftValueReadA shiftValueReadB
  obtain ⟨_sourceUnary, valueUnary, depthUnary, shiftUnary, _substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sameValueRead : hsame valueReadA valueReadB :=
    cont_deterministic valueDepthReadA valueDepthReadB
  have sameSubstitutionRead : hsame substitutionReadA substitutionReadB :=
    cont_respects_hsame (hsame_refl shift) sameValueRead shiftValueReadA shiftValueReadB
  have valueReadAUnary : UnaryHistory valueReadA :=
    unary_cont_closed valueUnary depthUnary valueDepthReadA
  have valueReadBUnary : UnaryHistory valueReadB :=
    unary_cont_closed valueUnary depthUnary valueDepthReadB
  have substitutionReadAUnary : UnaryHistory substitutionReadA :=
    unary_cont_closed shiftUnary valueReadAUnary shiftValueReadA
  have substitutionReadBUnary : UnaryHistory substitutionReadB :=
    unary_cont_closed shiftUnary valueReadBUnary shiftValueReadB
  exact
    ⟨sameValueRead, sameSubstitutionRead, valueReadAUnary, valueReadBUnary,
      substitutionReadAUnary, substitutionReadBUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
