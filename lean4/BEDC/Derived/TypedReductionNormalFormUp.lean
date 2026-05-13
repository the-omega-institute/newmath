import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TypedReductionNormalFormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TypedReductionNormalFormPacket [AskSetup] [PackageSetup]
    (term judgment membership reduction normal transport continuation provenance name endpoint : BHist)
    (mark : BMark) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory judgment ∧ UnaryHistory membership ∧
    UnaryHistory reduction ∧ UnaryHistory normal ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        UnaryHistory endpoint ∧ Ext term mark membership ∧ Cont membership reduction normal ∧
          Cont normal continuation endpoint ∧ hsame normal endpoint ∧
            hsame provenance endpoint ∧ hsame name endpoint ∧ PkgSig bundle endpoint pkg

theorem TypedReductionNormalFormPacket_namecert_obligations [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name
      endpoint : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TypedReductionNormalFormPacket term judgment membership reduction normal transport
              continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row normal)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        Ext term mark membership ∧ Cont membership reduction normal ∧
          Cont normal continuation endpoint := by
  -- BEDC touchpoint anchor: BHist Ext Cont hsame SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨_termUnary, _judgmentUnary, _membershipUnary, _reductionUnary, _normalUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    membershipRow, reductionRow, endpointRow, normalSameEndpoint, provenanceSameEndpoint,
    _nameSameEndpoint, endpointPkg⟩ := packet
  have endpointSameNormal : hsame endpoint normal :=
    hsame_symm normalSameEndpoint
  have endpointSameProvenance : hsame endpoint provenance :=
    hsame_symm provenanceSameEndpoint
  have certCore :
      NameCert
        (fun row : BHist =>
          TypedReductionNormalFormPacket term judgment membership reduction normal transport
            continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro packetWitness (hsame_refl endpoint))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            TypedReductionNormalFormPacket term judgment membership reduction normal transport
              continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row normal)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact hsame_trans sourceRow.right endpointSameNormal
      ledger_sound := by
        intro _row sourceRow
        exact And.intro (hsame_trans sourceRow.right endpointSameProvenance) endpointPkg
    }
  exact ⟨semantic, membershipRow, reductionRow, endpointRow⟩

theorem TypedReductionNormalFormPacket_subject_reduction_seal [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name
      endpoint : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      Ext term mark membership ∧ Cont membership reduction normal ∧
        Cont normal continuation endpoint ∧ hsame normal endpoint ∧
          hsame provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Ext Cont hsame PkgSig
  intro packet
  obtain ⟨_termUnary, _judgmentUnary, _membershipUnary, _reductionUnary, _normalUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    membershipRow, reductionRow, endpointRow, normalSameEndpoint, provenanceSameEndpoint,
    _nameSameEndpoint, endpointPkg⟩ := packet
  exact
    ⟨membershipRow, reductionRow, endpointRow, normalSameEndpoint, provenanceSameEndpoint,
      endpointPkg⟩

theorem TypedReductionNormalFormPacket_route_exactness [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name
      endpoint normal' endpoint' : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      Cont membership reduction normal' ->
        Cont normal' continuation endpoint' -> hsame normal normal' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro packet reductionRead continuationRead
  obtain ⟨_termUnary, _judgmentUnary, _membershipUnary, _reductionUnary, _normalUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    _membershipExt, reductionRow, endpointRow, _normalSameEndpoint, _provenanceSameEndpoint,
    _nameSameEndpoint, _endpointPkg⟩ := packet
  have normalExact : hsame normal normal' :=
    cont_deterministic reductionRow reductionRead
  have endpointExact : hsame endpoint endpoint' := by
    cases normalExact
    exact cont_deterministic endpointRow continuationRead
  exact ⟨normalExact, endpointExact⟩

theorem TypedReductionNormalFormPacket_terminal_boundary_nonescape [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name
      endpoint endpoint' : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      Cont normal continuation endpoint' ->
        hsame endpoint endpoint' ∧ hsame normal endpoint' ∧ UnaryHistory endpoint' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet endpointRead
  obtain ⟨_termUnary, _judgmentUnary, _membershipUnary, _reductionUnary, normalUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, endpointUnary,
    _membershipExt, _reductionRow, endpointRow, normalSameEndpoint, _provenanceSameEndpoint,
    _nameSameEndpoint, _endpointPkg⟩ := packet
  have endpointExact : hsame endpoint endpoint' :=
    cont_deterministic endpointRow endpointRead
  have normalSameEndpoint' : hsame normal endpoint' :=
    hsame_trans normalSameEndpoint endpointExact
  have endpointUnary' : UnaryHistory endpoint' := by
    cases endpointExact
    exact endpointUnary
  exact ⟨endpointExact, normalSameEndpoint', endpointUnary'⟩

theorem TypedReductionNormalFormPacket_transport_stability [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name endpoint
      normalPrime endpointPrime : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      Cont membership reduction normalPrime ->
        Cont normalPrime continuation endpointPrime ->
          TypedReductionNormalFormPacket term judgment membership reduction normalPrime transport
              continuation provenance name endpointPrime mark bundle pkg ∧
            hsame normal normalPrime ∧ hsame endpoint endpointPrime := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg
  intro packet membershipReductionPrime normalPrimeContinuation
  have exactRows :
      hsame normal normalPrime ∧ hsame endpoint endpointPrime :=
    TypedReductionNormalFormPacket_route_exactness packet membershipReductionPrime
      normalPrimeContinuation
  obtain ⟨normalSamePrime, endpointSamePrime⟩ := exactRows
  obtain ⟨termUnary, judgmentUnary, membershipUnary, reductionUnary, normalUnary,
    transportUnary, continuationUnary, provenanceUnary, nameUnary, endpointUnary,
    membershipExt, _membershipReduction, _normalContinuation, normalSameEndpoint,
    provenanceSameEndpoint, nameSameEndpoint, endpointPkg⟩ := packet
  have normalPrimeUnary : UnaryHistory normalPrime :=
    unary_transport normalUnary normalSamePrime
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_transport endpointUnary endpointSamePrime
  have normalPrimeSameEndpointPrime : hsame normalPrime endpointPrime :=
    hsame_trans (hsame_symm normalSamePrime) (hsame_trans normalSameEndpoint endpointSamePrime)
  have provenanceSameEndpointPrime : hsame provenance endpointPrime :=
    hsame_trans provenanceSameEndpoint endpointSamePrime
  have nameSameEndpointPrime : hsame name endpointPrime :=
    hsame_trans nameSameEndpoint endpointSamePrime
  have endpointPrimePkg : PkgSig bundle endpointPrime pkg := by
    cases endpointSamePrime
    exact endpointPkg
  exact
    ⟨⟨termUnary, judgmentUnary, membershipUnary, reductionUnary, normalPrimeUnary,
        transportUnary, continuationUnary, provenanceUnary, nameUnary, endpointPrimeUnary,
        membershipExt, membershipReductionPrime, normalPrimeContinuation,
        normalPrimeSameEndpointPrime, provenanceSameEndpointPrime, nameSameEndpointPrime,
        endpointPrimePkg⟩,
      normalSamePrime, endpointSamePrime⟩

end BEDC.Derived.TypedReductionNormalFormUp
