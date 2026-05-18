import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_core_refusal_host_quotient_exclusion
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          Cont h c endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory h ∧
                UnaryHistory c ∧ UnaryHistory refusalRead ∧ UnaryHistory endpoint ∧
                  Cont e a v ∧ Cont v h refusalRead ∧ Cont h c endpoint ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eAV vHRefusal hCEndpoint endpointPkg
  obtain ⟨eUnary, aUnary, _tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary hCEndpoint
  exact
    ⟨eUnary, aUnary, vUnary, hUnary, cUnary, refusalUnary, endpointUnary, eAV,
      vHRefusal, hCEndpoint, pPkg, endpointPkg, hN⟩

theorem QuotientSoundnessBoundaryCoreRefusalHostQuotientExclusion [AskSetup]
    [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        hsame row consumer)
                    (fun row : BHist =>
                      Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                        Cont h c row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                        PkgSig bundle transportRead pkg ∧ PkgSig bundle consumer pkg ∧
                          hsame h n)
                    hsame ∧
                    UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                      UnaryHistory consumer ∧ Cont v t refusalRead ∧
                        Cont t h transportRead ∧ Cont h c consumer ∧
                          PkgSig bundle refusalRead pkg ∧ PkgSig bundle transportRead pkg ∧
                            PkgSig bundle consumer pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
            hsame row consumer)
        (fun row : BHist =>
          Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧ Cont h c row)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
            PkgSig bundle transportRead pkg ∧ PkgSig bundle consumer pkg ∧ hsame h n)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer
        (And.intro carrierWitness (hsame_refl consumer))
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
      intro row source
      exact
        ⟨eAV, vTRefusal, tHTransport,
          cont_result_hsame_transport hCConsumer (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport consumerUnary (hsame_symm source.right), refusalPkg,
          transportPkg, consumerPkg, hN⟩
  }
  exact
    ⟨cert, refusalUnary, transportUnary, consumerUnary, vTRefusal, tHTransport, hCConsumer,
      refusalPkg, transportPkg, consumerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
