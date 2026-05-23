import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem FiniteLebesgueNumberDyadicRadiusWindowAdmissionRadiusCarrierSource
    [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius radiusRead ->
        Cont route nameRow rootRead ->
          PkgSig bundle rootRead pkg ->
            UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory radiusRead ∧
              UnaryHistory rootRead ∧ Cont cover radius radiusRead ∧
                Cont route nameRow rootRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusRead routeNameRoot rootPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  exact
    ⟨coverUnary, radiusUnary, radiusReadUnary, rootReadUnary, coverRadiusRead,
      routeNameRoot, provenancePkg, rootPkg⟩

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

theorem FiniteLebesgueNumberPhaseRealRadiusWindowFaceMinimality [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead realSeal
      outsideRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh dyadicRead →
        Cont dyadicRead window streamRead →
          Cont streamRead nameRow realSeal →
            hsame outsideRead realSeal →
              PkgSig bundle realSeal pkg →
                UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧ UnaryHistory realSeal ∧
                  UnaryHistory outsideRead ∧ Cont radius mesh dyadicRead ∧
                    Cont dyadicRead window streamRead ∧ Cont streamRead nameRow realSeal ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadicRead ∨ hsame row streamRead ∨
                            hsame row realSeal ∨ hsame row outsideRead)
                        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshDyadic dyadicWindowStream streamNameReal sameOutsideReal realPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed streamUnary nameRowUnary streamNameReal
  have outsideUnary : UnaryHistory outsideRead :=
    unary_transport_symm realUnary sameOutsideReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row realSeal ∨
            hsame row outsideRead)
        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }
  exact
    ⟨dyadicUnary, streamUnary, realUnary, outsideUnary, radiusMeshDyadic, dyadicWindowStream,
      streamNameReal, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
