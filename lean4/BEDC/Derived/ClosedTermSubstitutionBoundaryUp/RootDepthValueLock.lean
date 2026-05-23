import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootDepthValueLock [AskSetup] [PackageSetup]
    {source value depth shift substitution shiftRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          PkgSig bundle substitutionRead pkg ->
            hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
              UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                UnaryHistory shiftRead ∧ UnaryHistory substitutionRead ∧
                  PkgSig bundle substitutionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead substitutionReadPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, _substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueShiftRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed shiftReadUnary depthUnary shiftReadDepthSubstitutionRead
  exact
    ⟨sameShiftRead, sameSubstitutionRead, sourceUnary, valueUnary, depthUnary,
      shiftReadUnary, substitutionReadUnary, substitutionReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
