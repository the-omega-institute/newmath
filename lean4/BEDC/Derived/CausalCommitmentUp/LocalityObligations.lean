import BEDC.Derived.CausalCommitmentUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CausalCommitmentLocalityObligations [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        Cont locality routeRead observerRead ->
          PkgSig bundle observerRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                    transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
                (fun row : BHist =>
                  Cont observed regularity gap ∧ Cont gap forward continuation ∧
                    Cont forward locality localCert ∧ hsame row localCert)
                (fun row : BHist =>
                  PkgSig bundle localCert pkg ∧ PkgSig bundle observerRead pkg ∧
                    hsame row localCert)
                hsame ∧
              UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
                UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory routeRead ∧
                  UnaryHistory observerRead ∧ Cont observed regularity gap ∧
                    Cont gap forward continuation ∧ Cont forward locality localCert ∧
                      Cont continuation localCert routeRead ∧
                        Cont locality routeRead observerRead ∧
                          PkgSig bundle localCert pkg ∧ PkgSig bundle observerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertRoute localityRouteObserver observerPkg
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed localityUnary routeReadUnary localityRouteObserver
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CausalCommitmentForwardGapCarrier observed regularity gap forward locality
              transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont observed regularity gap ∧ Cont gap forward continuation ∧
              Cont forward locality localCert ∧ hsame row localCert)
          (fun row : BHist =>
            PkgSig bundle localCert pkg ∧ PkgSig bundle observerRead pkg ∧
              hsame row localCert)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert ⟨carrierWitness, hsame_refl localCert⟩
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
        intro _row _other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityLocalCert,
          source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨localCertPkg, observerPkg, source.right⟩
  }
  exact
    ⟨cert, observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      routeReadUnary, observerReadUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityLocalCert, continuationLocalCertRoute, localityRouteObserver,
      localCertPkg, observerPkg⟩

end BEDC.Derived.CausalCommitmentUp
