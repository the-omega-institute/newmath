import BEDC.Derived.FiniteLebesgueNumberUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealRadiusWindowAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh dyadicRead ->
        Cont dyadicRead window streamRead ->
          PkgSig bundle streamRead pkg ->
            UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory dyadicRead ∧
              UnaryHistory window ∧ UnaryHistory streamRead ∧ Cont radius mesh dyadicRead ∧
                Cont dyadicRead window streamRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle streamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshDyadic dyadicWindowStream streamPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  exact
    ⟨radiusUnary, meshUnary, dyadicUnary, windowUnary, streamUnary, radiusMeshDyadic,
      dyadicWindowStream, provenancePkg, streamPkg⟩

theorem FiniteLebesgueNumberOpenPhaseRootUnblockChoiceRefusal [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory rootRead ∧ hsame rootRead (append route nameRow) ∧
            Cont route nameRow rootRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle rootRead pkg ∧
                (Cont rootRead (BHist.e0 hostTail) route -> False) ∧
                  (Cont rootRead (BHist.e1 hostTail) route -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier routeNameRoot rootPkg
  obtain ⟨_coverUnary, _windowUnary, _radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  exact
    ⟨rootUnary, routeNameRoot, routeNameRoot, provenancePkg, rootPkg,
      fun hostReturn => cont_mutual_extension_right_tail_absurd.left routeNameRoot hostReturn,
      fun hostReturn => cont_mutual_extension_right_tail_absurd.right routeNameRoot hostReturn⟩

end BEDC.Derived.FiniteLebesgueNumberUp
