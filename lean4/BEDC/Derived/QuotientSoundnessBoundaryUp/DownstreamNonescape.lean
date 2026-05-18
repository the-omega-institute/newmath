import BEDC.Derived.QuotientSoundnessBoundaryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_downstream_nonescape [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer downstreamRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont transportRead consumer downstreamRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle transportRead pkg ->
                  PkgSig bundle downstreamRead pkg ->
                    UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory refusalRead ∧
                        UnaryHistory transportRead ∧ UnaryHistory consumer ∧
                          UnaryHistory downstreamRead ∧ Cont e a v ∧ Cont e t h ∧
                            Cont v t refusalRead ∧ Cont t h transportRead ∧
                              Cont h c consumer ∧ Cont transportRead consumer downstreamRead ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle refusalRead pkg ∧
                                  PkgSig bundle transportRead pkg ∧
                                    PkgSig bundle downstreamRead pkg ∧ hsame h n ∧
                                      (Cont downstreamRead (BHist.e0 hostTail) transportRead ->
                                        False) ∧
                                        (Cont downstreamRead (BHist.e1 hostTail)
                                            transportRead ->
                                          False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer transportConsumerDownstream refusalPkg
    transportPkg downstreamPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, _nUnary, eAV, eTH,
    _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed transportUnary consumerUnary transportConsumerDownstream
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, refusalUnary, transportUnary,
      consumerUnary, downstreamUnary, eAV, eTH, vTRefusal, tHTransport, hCConsumer,
      transportConsumerDownstream, pPkg, refusalPkg, transportPkg, downstreamPkg, hN,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left transportConsumerDownstream hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right transportConsumerDownstream hostReturn)⟩

theorem QuotientSoundnessBoundary_downstream_representative_nonescape_certificate
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer downstreamRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont transportRead consumer downstreamRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle transportRead pkg ->
                  PkgSig bundle downstreamRead pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                          hsame row downstreamRead)
                      (fun row : BHist =>
                        Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                          Cont h c consumer ∧ Cont transportRead consumer row ∧
                            PkgSig bundle downstreamRead pkg)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle downstreamRead pkg ∧
                            (Cont row (BHist.e0 hostTail) transportRead -> False) ∧
                              (Cont row (BHist.e1 hostTail) transportRead -> False))
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport hCConsumer transportConsumerDownstream refusalPkg
    transportPkg downstreamPkg
  have carrierWitness : QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg :=
    carrier
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    eAV, _eTH, _hCN, pPkg, _nPkg, _hN⟩ := carrier
  have downstreamFacts :=
    QuotientSoundnessBoundary_downstream_nonescape (hostTail := hostTail) carrierWitness
      vTRefusal tHTransport hCConsumer transportConsumerDownstream refusalPkg transportPkg
      downstreamPkg
  obtain ⟨_eUnaryD, _aUnaryD, _tUnaryD, _vUnaryD, _hUnaryD, _cUnaryD, _refusalUnary,
    _transportUnary, _consumerUnary, downstreamUnary, _eAVD, _eTHD, _vTRefusalD,
    _tHTransportD, _hCConsumerD, _transportConsumerDownstreamD, _pPkgD, _refusalPkgD,
    _transportPkgD, _downstreamPkgD, _hND, noZero, noOne⟩ := downstreamFacts
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro downstreamRead (And.intro carrierWitness (hsame_refl downstreamRead))
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
        ⟨eAV, vTRefusal, tHTransport, hCConsumer,
          cont_result_hsame_transport transportConsumerDownstream
            (hsame_symm source.right),
          downstreamPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport downstreamUnary (hsame_symm source.right), pPkg, downstreamPkg,
          (fun hostReturn =>
            noZero
              (cont_hsame_transport source.right (hsame_refl (BHist.e0 hostTail))
                (hsame_refl transportRead) hostReturn)),
          (fun hostReturn =>
            noOne
              (cont_hsame_transport source.right (hsame_refl (BHist.e1 hostTail))
                (hsame_refl transportRead) hostReturn))⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
