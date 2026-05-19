import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CausalCommitmentForwardGapScopePackage [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      Cont continuation localCert routeRead →
        Cont routeRead locality scopeRead →
          PkgSig bundle scopeRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row observed ∨ hsame row regularity ∨ hsame row gap ∨
                    hsame row forward ∨ hsame row locality ∨ hsame row scopeRead)
                (fun row : BHist => PkgSig bundle scopeRead pkg ∧ hsame row scopeRead)
                hsame ∧
              UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
                UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory routeRead ∧
                  UnaryHistory scopeRead ∧ Cont observed regularity gap ∧
                    Cont gap forward continuation ∧ Cont forward locality localCert ∧
                      Cont continuation localCert routeRead ∧
                        Cont routeRead locality scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier continuationLocalRoute routeLocalityScope scopePkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocal : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, _localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalRoute
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed routeReadUnary localityUnary routeLocalityScope
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observed ∨ hsame row regularity ∨ hsame row gap ∨
              hsame row forward ∨ hsame row locality ∨ hsame row scopeRead)
          (fun row : BHist => PkgSig bundle scopeRead pkg ∧ hsame row scopeRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeReadUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    · intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    · intro _row source
      exact ⟨scopePkg, source.left⟩
  exact
    ⟨cert, observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      routeReadUnary, scopeReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocal, continuationLocalRoute, routeLocalityScope⟩

theorem CausalCommitmentForwardGapCarrier_locality_replay_package [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont locality localCert localityRead ->
        PkgSig bundle localityRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory localCert ∧
              UnaryHistory localityRead ∧ Cont observed regularity gap ∧
                Cont gap forward continuation ∧ Cont forward locality localCert ∧
                  Cont locality localCert localityRead ∧ PkgSig bundle localCert pkg ∧
                    PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier localityLocalCertRead localityReadPkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary localCertUnary localityLocalCertRead
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary, localCertUnary,
      localityReadUnary, observedRegularityGap, gapForwardContinuation, forwardLocalityName,
      localityLocalCertRead, localCertPkg, localityReadPkg⟩

end BEDC.Derived.CausalCommitmentUp
