import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DedekindCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DedekindCutCarrier [AskSetup] [PackageSetup]
    (lower upper inhabited rounded located disjoint embedding transport routes provenance nameCert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory inhabited ∧ UnaryHistory rounded ∧
    UnaryHistory located ∧ UnaryHistory disjoint ∧ UnaryHistory embedding ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont lower upper inhabited ∧ Cont inhabited rounded located ∧
          Cont located disjoint embedding ∧ Cont embedding transport routes ∧
            Cont routes nameCert provenance ∧ PkgSig bundle provenance pkg

theorem DedekindCutCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              DedekindCutCarrier lower upper inhabited rounded located disjoint embedding
                transport routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont lower upper inhabited)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory inhabited ∧
          UnaryHistory rounded ∧ UnaryHistory located ∧ UnaryHistory disjoint ∧
            UnaryHistory embedding ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
              UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont lower upper inhabited ∧
                Cont inhabited rounded located ∧ Cont located disjoint embedding ∧
                  Cont embedding transport routes ∧ Cont routes nameCert provenance ∧
                    PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
    embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
    inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩ :=
      carrier
  have carrierRows :
      DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg :=
    ⟨lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
      embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
      inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩
  have sourceProvenance :
      (fun row : BHist =>
        hsame row provenance ∧
          DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport
            routes provenance nameCert bundle pkg) provenance := by
    exact ⟨hsame_refl provenance, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row provenance ∧
            DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport
              routes provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro provenance sourceProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              DedekindCutCarrier lower upper inhabited rounded located disjoint embedding
                transport routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont lower upper inhabited)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact ⟨source.left, lowerUpper⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
      embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
      inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩

theorem DedekindCutCarrier_located_rounded_cut_laws [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg ->
      UnaryHistory inhabited ∧ UnaryHistory rounded ∧ UnaryHistory located ∧
        UnaryHistory disjoint ∧ Cont lower upper inhabited ∧
          Cont inhabited rounded located ∧ Cont located disjoint embedding ∧
            PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_lowerUnary, _upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
    _embeddingUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    lowerUpperInhabited, inhabitedRoundedLocated, locatedDisjointEmbedding,
    _embeddingTransportRoutes, _routesNameCertProvenance, provenancePkg⟩ := carrier
  exact
    ⟨inhabitedUnary, roundedUnary, locatedUnary, disjointUnary, lowerUpperInhabited,
      inhabitedRoundedLocated, locatedDisjointEmbedding, provenancePkg⟩

theorem DedekindCutCarrier_rational_embedding_boundary [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance nameCert
      lowerBoundary upperBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes provenance
        nameCert bundle pkg ->
      Cont embedding lower lowerBoundary -> Cont embedding upper upperBoundary ->
        PkgSig bundle provenance pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory embedding ∧
            UnaryHistory lowerBoundary ∧ UnaryHistory upperBoundary ∧
              Cont embedding lower lowerBoundary ∧ Cont embedding upper upperBoundary ∧
                PkgSig bundle provenance pkg := by
  intro carrier lowerBoundaryCont upperBoundaryCont provenancePkg
  obtain ⟨lowerUnary, upperUnary, _inhabitedUnary, _roundedUnary, _locatedUnary,
    _disjointUnary, embeddingUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _lowerUpper, _inhabitedRounded, _locatedDisjoint, _embeddingTransport,
    _routesNameCert, _carrierPkg⟩ := carrier
  have lowerBoundaryUnary : UnaryHistory lowerBoundary :=
    unary_cont_closed embeddingUnary lowerUnary lowerBoundaryCont
  have upperBoundaryUnary : UnaryHistory upperBoundary :=
    unary_cont_closed embeddingUnary upperUnary upperBoundaryCont
  exact
    ⟨lowerUnary, upperUnary, embeddingUnary, lowerBoundaryUnary, upperBoundaryUnary,
      lowerBoundaryCont, upperBoundaryCont, provenancePkg⟩

theorem DedekindCutCarrier_realup_comparison_handoff [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance nameCert
      realSeal comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg ->
      Cont embedding transport realSeal ->
        Cont realSeal routes comparisonRead ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory embedding ∧
            UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory realSeal ∧
              UnaryHistory comparisonRead ∧ Cont embedding transport realSeal ∧
                Cont realSeal routes comparisonRead ∧ PkgSig bundle provenance pkg := by
  intro carrier realSealRoute comparisonRoute
  obtain ⟨lowerUnary, upperUnary, _inhabitedUnary, _roundedUnary, _locatedUnary,
    _disjointUnary, embeddingUnary, transportUnary, routesUnary, _provenanceUnary,
    _nameCertUnary, _lowerUpper, _inhabitedRounded, _locatedDisjoint,
    _embeddingTransport, _routesNameCert, provenancePkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed embeddingUnary transportUnary realSealRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed realSealUnary routesUnary comparisonRoute
  exact
    ⟨lowerUnary, upperUnary, embeddingUnary, transportUnary, routesUnary, realSealUnary,
      comparisonReadUnary, realSealRoute, comparisonRoute, provenancePkg⟩

theorem DedekindCutCarrier_quotient_free_boundary [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance nameCert
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg ->
      Cont embedding transport comparisonRead ->
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory embedding ∧
          UnaryHistory transport ∧ UnaryHistory comparisonRead ∧
            Cont located disjoint embedding ∧ Cont embedding transport comparisonRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier comparisonCont
  obtain ⟨lowerUnary, upperUnary, _inhabitedUnary, _roundedUnary, _locatedUnary,
    _disjointUnary, embeddingUnary, transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _lowerUpper, _inhabitedRounded, locatedDisjoint,
    _embeddingTransport, _routesNameCert, provenancePkg⟩ := carrier
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed embeddingUnary transportUnary comparisonCont
  exact
    ⟨lowerUnary, upperUnary, embeddingUnary, transportUnary, comparisonReadUnary,
      locatedDisjoint, comparisonCont, provenancePkg⟩

end BEDC.Derived.DedekindCutUp
