import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicRoundingWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicRoundingWindowCarrier [AskSetup] [PackageSetup]
    (stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory precision ∧ UnaryHistory endpoint ∧
    UnaryHistory readback ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
      Cont precision stream endpoint ∧ Cont stream endpoint readback ∧
        Cont readback regular realSeal ∧ PkgSig bundle provenance pkg ∧
          hsame localName stream ∧ hsame localName provenance

theorem DyadicRoundingWindowCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal
                transport route provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
              hsame row readback ∨ hsame row regular ∨ hsame row realSeal)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg) hsame ∧
        UnaryHistory stream ∧ UnaryHistory precision ∧ UnaryHistory endpoint ∧
          UnaryHistory readback ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
            Cont precision stream endpoint ∧ Cont stream endpoint readback ∧
              Cont readback regular realSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨streamUnary, precisionUnary, endpointUnary, readbackUnary, regularUnary, realSealUnary,
      precisionStreamEndpoint, streamEndpointReadback, readbackRegularRealSeal, provenancePkg,
      localNameStream, localNameProvenance⟩ := carrier
  have carrierProof :
      DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg :=
    ⟨streamUnary, precisionUnary, endpointUnary, readbackUnary, regularUnary, realSealUnary,
      precisionStreamEndpoint, streamEndpointReadback, readbackRegularRealSeal, provenancePkg,
      localNameStream, localNameProvenance⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro localName ⟨hsame_refl localName, carrierProof⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro row sourceRow
        exact Or.inl (hsame_trans sourceRow.left localNameStream)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨hsame_trans sourceRow.left localNameProvenance, provenancePkg⟩
    }
  · exact
      ⟨streamUnary, precisionUnary, endpointUnary, readbackUnary, regularUnary, realSealUnary,
        precisionStreamEndpoint, streamEndpointReadback, readbackRegularRealSeal, provenancePkg⟩

theorem DyadicRoundingWindowCarrier_error_bound [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row readback ∨ hsame row regular ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precision stream endpoint ∧ Cont stream endpoint readback ∧
              Cont readback regular realSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory endpoint ∧ UnaryHistory readback ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_streamUnary, _precisionUnary, endpointUnary, readbackUnary, _regularUnary,
      realSealUnary, precisionStreamEndpoint, streamEndpointReadback, readbackRegularRealSeal,
      provenancePkg, _localNameStream, _localNameProvenance⟩ := carrier
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro readback ⟨hsame_refl readback, readbackUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inl sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, precisionStreamEndpoint, streamEndpointReadback,
            readbackRegularRealSeal, provenancePkg⟩
    }
  · exact ⟨endpointUnary, readbackUnary, realSealUnary⟩

theorem DyadicRoundingWindowCarrier_readback_handoff [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row regular ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback regular realSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory readback ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
          Cont readback regular realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_streamUnary, _precisionUnary, _endpointUnary, readbackUnary, regularUnary,
      realSealUnary, _precisionStreamEndpoint, _streamEndpointReadback,
      readbackRegularRealSeal, provenancePkg, _localNameStream, _localNameProvenance⟩ :=
        carrier
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, readbackRegularRealSeal, provenancePkg⟩
    }
  · exact ⟨readbackUnary, regularUnary, realSealUnary, readbackRegularRealSeal⟩

theorem DyadicRoundingWindowCarrier_precision_classification [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory endpoint ∧
        Cont precision stream endpoint ∧ Cont stream endpoint readback ∧
          hsame localName stream := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier
  obtain
    ⟨streamUnary, precisionUnary, endpointUnary, _readbackUnary, _regularUnary, _realSealUnary,
      precisionStreamEndpoint, streamEndpointReadback, _readbackRegularRealSeal, _provenancePkg,
      localNameStream, _localNameProvenance⟩ := carrier
  exact
    ⟨precisionUnary, streamUnary, endpointUnary, precisionStreamEndpoint,
      streamEndpointReadback, localNameStream⟩

theorem DyadicRoundingWindowCarrier_adjacent_endpoint_compatibility [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      UnaryHistory endpoint ∧ UnaryHistory readback ∧ Cont stream endpoint readback ∧
        hsame localName provenance := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier
  obtain
    ⟨_streamUnary, _precisionUnary, endpointUnary, readbackUnary, _regularUnary, _realSealUnary,
      _precisionStreamEndpoint, streamEndpointReadback, _readbackRegularRealSeal, _provenancePkg,
      _localNameStream, localNameProvenance⟩ := carrier
  exact ⟨endpointUnary, readbackUnary, streamEndpointReadback, localNameProvenance⟩

theorem DyadicRoundingWindowCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
              hsame row readback ∨ hsame row regular ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback regular realSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory regular ∧ UnaryHistory realSeal ∧ Cont readback regular realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_streamUnary, _precisionUnary, _endpointUnary, readbackUnary, regularUnary,
      realSealUnary, _precisionStreamEndpoint, _streamEndpointReadback,
      readbackRegularRealSeal, provenancePkg, _localNameStream, _localNameProvenance⟩ :=
        carrier
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, readbackRegularRealSeal, provenancePkg⟩
    }
  · exact ⟨regularUnary, realSealUnary, readbackRegularRealSeal⟩

theorem DyadicRoundingWindowCarrier_precision_window_obligation [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
              hsame row readback ∨ hsame row regular ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precision stream endpoint ∧ Cont stream endpoint readback ∧
              PkgSig bundle provenance pkg)
          hsame ∧ UnaryHistory stream ∧ UnaryHistory precision ∧ UnaryHistory endpoint ∧
        Cont precision stream endpoint ∧ Cont stream endpoint readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨streamUnary, precisionUnary, endpointUnary, _readbackUnary, _regularUnary, _realSealUnary,
      precisionStreamEndpoint, streamEndpointReadback, _readbackRegularRealSeal, provenancePkg,
      _localNameStream, _localNameProvenance⟩ := carrier
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inl sourceRow.left))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, precisionStreamEndpoint, streamEndpointReadback, provenancePkg⟩
    }
  · exact
      ⟨streamUnary, precisionUnary, endpointUnary, precisionStreamEndpoint,
        streamEndpointReadback⟩

theorem DyadicRoundingWindowCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          (fun row : BHist =>
            hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
              hsame row readback ∨ hsame row regular ∨ hsame row realSeal ∨
                hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
            hsame row provenance)
          hsame ∧
        UnaryHistory provenance ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨streamUnary, _precisionUnary, _endpointUnary, _readbackUnary, _regularUnary,
      _realSealUnary, _precisionStreamEndpoint, _streamEndpointReadback,
      _readbackRegularRealSeal, provenancePkg, localNameStream,
      localNameProvenance⟩ := carrier
  have streamProvenance : hsame stream provenance :=
    hsame_trans (hsame_symm localNameStream) localNameProvenance
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport streamUnary streamProvenance
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro provenance ⟨hsame_refl provenance, provenancePkg⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))))
      ledger_sound := by
        intro row sourceRow
        exact
          ⟨unary_transport provenanceUnary (hsame_symm sourceRow.left), sourceRow.right,
            sourceRow.left⟩
    }
  · exact ⟨provenanceUnary, provenancePkg⟩

theorem DyadicRoundingWindowCarrier_scoped_consumer_boundary [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      Cont realSeal provenance consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
                  hsame row readback ∨ hsame row regular ∨ hsame row realSeal ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont precision stream endpoint ∧
                  Cont stream endpoint readback ∧ Cont readback regular realSeal ∧
                    Cont realSeal provenance consumerRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumerRead pkg)
              hsame ∧
            UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier realSealProvenanceConsumer consumerPkg
  obtain
    ⟨streamUnary, precisionUnary, _endpointUnary, _readbackUnary, _regularUnary,
      realSealUnary, precisionStreamEndpoint, streamEndpointReadback,
      readbackRegularRealSeal, provenancePkg, localNameStream,
      localNameProvenance⟩ := carrier
  have streamProvenance : hsame stream provenance :=
    hsame_trans (hsame_symm localNameStream) localNameProvenance
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport streamUnary streamProvenance
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceConsumer
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, precisionStreamEndpoint, streamEndpointReadback,
            readbackRegularRealSeal, realSealProvenanceConsumer, provenancePkg, consumerPkg⟩
    }
  · exact consumerUnary

theorem DyadicRoundingWindowCarrier_scoped_kernel_dependencies [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      Cont realSeal provenance scopedRead ->
        PkgSig bundle scopedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
                  hsame row readback ∨ hsame row regular ∨ hsame row realSeal ∨
                    hsame row provenance ∨ hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont readback regular realSeal ∧
                  Cont realSeal provenance scopedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle scopedRead pkg)
              hsame ∧ UnaryHistory scopedRead ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier realSealProvenanceScoped scopedPkg
  obtain
    ⟨streamUnary, _precisionUnary, _endpointUnary, _readbackUnary, _regularUnary,
      realSealUnary, _precisionStreamEndpoint, _streamEndpointReadback,
      readbackRegularRealSeal, provenancePkg, localNameStream, localNameProvenance⟩ :=
        carrier
  have streamProvenance : hsame stream provenance :=
    hsame_trans (hsame_symm localNameStream) localNameProvenance
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport streamUnary streamProvenance
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceScoped
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, readbackRegularRealSeal, realSealProvenanceScoped,
            provenancePkg, scopedPkg⟩
    }
  · exact ⟨scopedUnary, provenancePkg, scopedPkg⟩

end BEDC.Derived.DyadicRoundingWindowUp
