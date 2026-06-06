import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootOperationDependency [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont shift valueClosed operationRead ->
            PkgSig bundle operationRead pkg ->
              UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                UnaryHistory operationRead ∧ Cont source value sourceClosed ∧
                  Cont value depth valueClosed ∧ Cont shift valueClosed operationRead ∧
                    PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceValueClosed valueDepthClosed shiftValueClosedOperation operationPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, _substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed shiftUnary valueClosedUnary shiftValueClosedOperation
  exact
    ⟨sourceClosedUnary, valueClosedUnary, operationUnary, sourceValueClosed,
      valueDepthClosed, shiftValueClosedOperation, operationPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
