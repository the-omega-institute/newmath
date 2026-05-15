import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def QuotientSoundnessBoundaryCarrier [AskSetup] [PackageSetup]
    (e a t v h c p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
      Cont e a v ∧ Cont e t h ∧ Cont h c n ∧ PkgSig bundle p pkg ∧
        PkgSig bundle n pkg ∧ hsame h n

theorem QuotientSoundnessBoundary_root_psame_route_totality [AskSetup] [PackageSetup]
    {e a t v h c p n endpoint : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => Cont e t h ∧ Cont h c row ∧ PkgSig bundle endpoint pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier hEndpoint endpointPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, _aUnary, tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have endpointUnary : UnaryHistory endpoint := unary_cont_closed hUnary cUnary hEndpoint
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrierWitness (hsame_refl endpoint))
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
      exact And.intro eTH
        (And.intro (cont_result_hsame_transport hEndpoint (hsame_symm source.right))
          endpointPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) endpointPkg
  }

theorem QuotientSoundnessBoundary_root_representative_refusal_totality
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          PkgSig bundle refusalRead pkg ->
            UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory refusalRead ∧
              Cont e a v ∧ Cont v h refusalRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle refusalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eAV vHRefusal refusalPkg
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have vUnary : UnaryHistory v := unary_cont_closed eUnary aUnary eAV
  have refusalUnary : UnaryHistory refusalRead := unary_cont_closed vUnary hUnary vHRefusal
  exact And.intro eUnary
    (And.intro aUnary
      (And.intro vUnary
        (And.intro refusalUnary
          (And.intro eAV
              (And.intro vHRefusal
                (And.intro pPkg (And.intro refusalPkg hN)))))))

theorem QuotientSoundnessBoundary_negative_refusal_certificate [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          PkgSig bundle refusalRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                  hsame row refusalRead)
              (fun row : BHist =>
                Cont e a v ∧ Cont v h row ∧ PkgSig bundle refusalRead pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle refusalRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier eAV vHRefusal refusalPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have vUnary : UnaryHistory v := unary_cont_closed eUnary aUnary eAV
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  exact {
    core := {
      carrier_inhabited := Exists.intro refusalRead
        (And.intro carrierWitness (hsame_refl refusalRead))
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
      exact And.intro eAV
        (And.intro (cont_result_hsame_transport vHRefusal (hsame_symm source.right))
          refusalPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport refusalUnary (hsame_symm source.right)) refusalPkg
  }

theorem QuotientSoundnessBoundary_cont_route_locality [AskSetup] [PackageSetup]
    {e a t v h c p n consumer : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont h c consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
            UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory consumer ∧ Cont e a v ∧
              Cont e t h ∧ Cont h c consumer ∧ PkgSig bundle n pkg ∧
                PkgSig bundle consumer pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier hCConsumer consumerPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary, eAV, eTH,
    _hCN, _pPkg, nPkg, hN⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, consumerUnary, eAV, eTH,
      hCConsumer, nPkg, consumerPkg, hN⟩

theorem QuotientSoundnessBoundaryCarrier_transport_replacement [AskSetup] [PackageSetup]
    {e a t v h c p n replacement : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont h c replacement ->
        PkgSig bundle replacement pkg ->
          UnaryHistory e ∧ UnaryHistory t ∧ UnaryHistory h ∧ UnaryHistory c ∧
            UnaryHistory replacement ∧ Cont e t h ∧ Cont h c replacement ∧
              PkgSig bundle replacement pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier replacementRoute replacementPkg
  obtain ⟨eUnary, _aUnary, tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have replacementUnary : UnaryHistory replacement :=
    unary_cont_closed hUnary cUnary replacementRoute
  exact
    ⟨eUnary, tUnary, hUnary, cUnary, replacementUnary, eTH, replacementRoute,
      replacementPkg, hN⟩

theorem QuotientSoundnessBoundary_consumer_route_certificate [AskSetup] [PackageSetup]
    {e a t v h c p n consumer : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont h c consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
            (fun row : BHist =>
              QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                hsame row consumer)
            (fun row : BHist => Cont e t h ∧ Cont h c row ∧ PkgSig bundle consumer pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumer pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier hCConsumer consumerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact {
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
      exact And.intro eTH
        (And.intro (cont_result_hsame_transport hCConsumer (hsame_symm source.right))
          consumerPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport consumerUnary (hsame_symm source.right)) consumerPkg
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
