import BEDC.Derived.BishopRealComparisonUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealComparisonCarrier [AskSetup] [PackageSetup]
    (bishop completion located dedekind realSeal readback transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bishop ∧ UnaryHistory completion ∧ UnaryHistory located ∧
    UnaryHistory dedekind ∧ UnaryHistory realSeal ∧ UnaryHistory readback ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont bishop readback realSeal ∧ Cont completion readback realSeal ∧
          Cont located readback realSeal ∧ Cont dedekind readback realSeal ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row name ∧ UnaryHistory row)
                (fun row : BHist => UnaryHistory row ∧ hsame row name)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                (fun row row' : BHist => hsame row row')

theorem BishopRealComparisonCarrier_cauchy_dedekind_boundary [AskSetup] [PackageSetup]
    {bishop completion located dedekind realSeal readback transport provenance name
      cutBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealComparisonCarrier bishop completion located dedekind realSeal readback transport
        provenance name bundle pkg ->
      Cont bishop completion readback ->
        Cont readback dedekind cutBoundary ->
          UnaryHistory bishop ∧ UnaryHistory readback ∧ UnaryHistory dedekind ∧
            UnaryHistory cutBoundary ∧ Cont bishop completion readback ∧
              Cont readback dedekind cutBoundary ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier cauchyReadbackRoute boundaryRoute
  obtain ⟨bishopUnary, _completionUnary, _locatedUnary, dedekindUnary, _realSealUnary,
    readbackUnary, _transportUnary, _provenanceUnary, _nameUnary, _bishopSealRoute,
      _completionSealRoute, _locatedSealRoute, _dedekindSealRoute, provenancePkg,
        _semanticCert⟩ := carrier
  have cutBoundaryUnary : UnaryHistory cutBoundary :=
    unary_cont_closed readbackUnary dedekindUnary boundaryRoute
  exact
    ⟨bishopUnary, readbackUnary, dedekindUnary, cutBoundaryUnary, cauchyReadbackRoute,
      boundaryRoute, provenancePkg⟩

theorem BishopRealComparisonCarrier_located_readback [AskSetup] [PackageSetup]
    {bishop completion located dedekind realSeal readback transport provenance name
      locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealComparisonCarrier bishop completion located dedekind realSeal readback transport
        provenance name bundle pkg ->
      Cont bishop readback realSeal ->
        Cont realSeal located locatedRead ->
          PkgSig bundle locatedRead pkg ->
            UnaryHistory bishop ∧ UnaryHistory located ∧ UnaryHistory realSeal ∧
              UnaryHistory locatedRead ∧ Cont bishop readback realSeal ∧
                Cont realSeal located locatedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier bishopReadSeal locatedRoute locatedPkg
  obtain ⟨bishopUnary, _completionUnary, locatedUnary, _dedekindUnary, realSealUnary,
    _readbackUnary, _transportUnary, _provenanceUnary, _nameUnary, _bishopSealRoute,
      _completionSealRoute, _locatedSealRoute, _dedekindSealRoute, provenancePkg,
        _semanticCert⟩ := carrier
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed realSealUnary locatedUnary locatedRoute
  exact
    ⟨bishopUnary, locatedUnary, realSealUnary, locatedReadUnary, bishopReadSeal,
      locatedRoute, provenancePkg, locatedPkg⟩

end BEDC.Derived.BishopRealComparisonUp
