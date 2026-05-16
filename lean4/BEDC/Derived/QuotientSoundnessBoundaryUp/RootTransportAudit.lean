import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_quotsound_exclusion [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          PkgSig bundle refusalRead pkg ->
            PkgSig bundle transportRead pkg ->
              UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory t ∧
                UnaryHistory h ∧ UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                  Cont e a v ∧ Cont e t h ∧ Cont v t refusalRead ∧
                    Cont t h transportRead ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle refusalRead pkg ∧ PkgSig bundle transportRead pkg ∧
                        hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport refusalPkg transportPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, _nUnary, eAV,
    eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  exact
    ⟨eUnary, aUnary, vUnary, tUnary, hUnary, refusalUnary, transportUnary, eAV,
      eTH, vTRefusal, tHTransport, pPkg, refusalPkg, transportPkg, hN⟩

theorem QuotientSoundnessBoundary_root_psame_transport_admission
    [AskSetup] [PackageSetup]
    {e a t v h c p n transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont t h transportRead ->
        PkgSig bundle transportRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                Cont t h transportRead ∧ hsame row transportRead)
            (fun row : BHist =>
              Cont e t h ∧ Cont t h row ∧ PkgSig bundle transportRead pkg)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle transportRead pkg ∧ hsame h n)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier tHTransport transportPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  exact {
    core := {
      carrier_inhabited := Exists.intro transportRead
        (And.intro carrierWitness (And.intro tHTransport (hsame_refl transportRead)))
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
        exact And.intro source.left
          (And.intro source.right.left
            (hsame_trans (hsame_symm sameRows) source.right.right))
    }
    pattern_sound := by
      intro row source
      exact And.intro eTH
        (And.intro (cont_result_hsame_transport tHTransport (hsame_symm source.right.right))
          transportPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport transportUnary (hsame_symm source.right.right))
        (And.intro transportPkg hN)
  }

theorem QuotientSoundnessBoundary_root_representative_refusal_certificate
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          PkgSig bundle refusalRead pkg ->
            PkgSig bundle transportRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                    Cont v t refusalRead ∧ Cont t h transportRead ∧
                      hsame row refusalRead)
                (fun row : BHist =>
                  Cont e a v ∧ Cont v t row ∧ Cont t h transportRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                    PkgSig bundle transportRead pkg ∧ hsame h n)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport refusalPkg transportPkg
  have sourceWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
        Cont v t refusalRead ∧ Cont t h transportRead ∧ hsame refusalRead refusalRead :=
    ⟨carrier, vTRefusal, tHTransport, hsame_refl refusalRead⟩
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, _hUnary, _cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  exact {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceWitness
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eAV,
          cont_result_hsame_transport source.right.left
            (hsame_symm source.right.right.right),
          source.right.right.left⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport refusalUnary (hsame_symm source.right.right.right),
          refusalPkg, transportPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
