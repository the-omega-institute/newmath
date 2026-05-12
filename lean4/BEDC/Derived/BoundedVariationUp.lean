import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedVariationCarrier [AskSetup] [PackageSetup]
    (interval partition endpoint dyadic variation refinement transport route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory partition ∧ UnaryHistory endpoint ∧
    UnaryHistory dyadic ∧ UnaryHistory variation ∧ UnaryHistory refinement ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont interval partition endpoint ∧
          Cont endpoint dyadic transport ∧ Cont partition dyadic variation ∧
            Cont variation refinement route ∧ Cont route provenance nameCert ∧
              hsame variation (append partition dyadic) ∧ PkgSig bundle provenance pkg

theorem BoundedVariationCarrier_variation_ledger_exactness [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edgeRead sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont endpoint dyadic edgeRead ->
        Cont variation refinement sumRead ->
          UnaryHistory edgeRead ∧ UnaryHistory sumRead ∧
            hsame variation (append partition dyadic) ∧ PkgSig bundle provenance pkg := by
  intro carrier edgeReadRow sumReadRow
  obtain ⟨_intervalUnary, _partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, variationSame, pkgSig⟩ := carrier
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary dyadicUnary edgeReadRow
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed variationUnary refinementUnary sumReadRow
  exact ⟨edgeReadUnary, sumReadUnary, variationSame, pkgSig⟩

theorem BoundedVariationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.BoundedVariationUp
