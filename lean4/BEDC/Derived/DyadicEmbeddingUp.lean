import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicEmbeddingCarrier [AskSetup] [PackageSetup]
    (dyadic stream readback realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
    UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont dyadic stream readback ∧
        Cont readback realSeal route ∧ Cont route provenance nameCert ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem DyadicEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {dyadic stream readback realSeal transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicEmbeddingCarrier dyadic stream readback realSeal transport route provenance nameCert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicEmbeddingCarrier dyadic stream readback realSeal transport route provenance
            nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
            UnaryHistory realSeal ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
        hsame := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨dyadicUnary, streamUnary, readbackUnary, realSealUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameCertUnary, _dyadicStreamReadback,
    _readbackRealSealRoute, _routeProvenanceNameCert, provenancePkg, _nameCertPkg⟩ :=
    carrier
  have sourceNameCert :
      (fun row : BHist =>
        DyadicEmbeddingCarrier dyadic stream readback realSeal transport route provenance
          nameCert bundle pkg ∧ hsame row nameCert) nameCert := by
    exact And.intro carrierWitness (hsame_refl nameCert)
  have core :
      NameCert
        (fun row : BHist =>
          DyadicEmbeddingCarrier dyadic stream readback realSeal transport route provenance
            nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro nameCert sourceNameCert
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHNameCert : hsame h nameCert := sourceH.right
        have sameKNameCert : hsame k nameCert :=
          hsame_trans (hsame_symm sameHK) sameHNameCert
        exact And.intro sourceH.left sameKNameCert
    }
  exact {
    core := core
    pattern_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport nameCertUnary (hsame_symm source.right)
      exact ⟨dyadicUnary, streamUnary, readbackUnary, realSealUnary, rowUnary⟩
    ledger_sound := by
      intro row source
      exact And.intro provenancePkg source.right
  }

theorem DyadicEmbeddingCarrier_constant_stream_readback [AskSetup] [PackageSetup]
    {dyadic stream readback realSeal transport route provenance nameCert station : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicEmbeddingCarrier dyadic stream readback realSeal transport route provenance nameCert
        bundle pkg ->
      Cont dyadic stream station ->
        Cont station readback route ->
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory station ∧
            UnaryHistory readback ∧ Cont dyadic stream station ∧
              Cont station readback route ∧ PkgSig bundle provenance pkg := by
  intro carrier dyadicStreamStation stationReadbackRoute
  obtain ⟨dyadicUnary, streamUnary, readbackUnary, _realSealUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameCertUnary, _dyadicStreamReadback,
    _readbackRealSealRoute, _routeProvenanceNameCert, provenancePkg, _nameCertPkg⟩ :=
    carrier
  have stationUnary : UnaryHistory station :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamStation
  exact ⟨dyadicUnary, streamUnary, stationUnary, readbackUnary, dyadicStreamStation,
    stationReadbackRoute, provenancePkg⟩

end BEDC.Derived.DyadicEmbeddingUp
