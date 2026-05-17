import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionFunctorPacket [AskSetup] [PackageSetup]
    (metric regular «seal» «monad» universal classifier transport nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory «seal» ∧ UnaryHistory «monad» ∧
    UnaryHistory universal ∧ UnaryHistory classifier ∧ UnaryHistory transport ∧
      UnaryHistory nameCert ∧ UnaryHistory endpoint ∧ Cont metric regular «seal» ∧
        Cont «monad» universal endpoint ∧ Cont classifier transport nameCert ∧
          PkgSig bundle endpoint pkg

theorem CauchyCompletionFunctorPacket_namecert_obligations [AskSetup] [PackageSetup]
    {metric regular «seal» «monad» universal classifier transport nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport nameCert
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory «seal» ∧ UnaryHistory «monad» ∧
          UnaryHistory universal ∧ Cont metric regular «seal» ∧ Cont «monad» universal endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
            nameCert endpoint bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
              nameCert endpoint bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨cert, metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, metricRegularSeal,
      monadUniversalEndpoint, endpointPkg⟩

theorem CauchyCompletionFunctorPacket_classifier_transport [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint classifier'
      transport' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      hsame classifier classifier' ->
        hsame transport transport' ->
          hsame nameCert nameCert' ->
            Cont classifier' transport' nameCert' ->
              CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier'
                  transport' nameCert' endpoint bundle pkg ∧
                UnaryHistory nameCert' ∧ PkgSig bundle endpoint pkg := by
  intro packet sameClassifier sameTransport sameNameCert classifierTransportNameCert'
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, classifierUnary,
    transportUnary, nameCertUnary, endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  exact
    ⟨⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, classifierUnary',
      transportUnary', nameCertUnary', endpointUnary, metricRegularSeal, monadUniversalEndpoint,
      classifierTransportNameCert', endpointPkg⟩, nameCertUnary', endpointPkg⟩

theorem CauchyCompletionFunctorPacket_unit_laws [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      unitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont metric sealRow unitRead ->
        PkgSig bundle unitRead pkg ->
          UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
            UnaryHistory monadRow ∧ UnaryHistory universal ∧ UnaryHistory unitRead ∧
              Cont metric regular sealRow ∧ Cont metric sealRow unitRead ∧
                Cont monadRow universal endpoint ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle unitRead pkg := by
  intro packet metricSealUnit unitPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed metricUnary sealUnary metricSealUnit
  exact
    ⟨metricUnary,
      regularUnary,
      sealUnary,
      monadUnary,
      universalUnary,
      unitUnary,
      metricRegularSeal,
      metricSealUnit,
      monadUniversalEndpoint,
      endpointPkg,
      unitPkg⟩

theorem CauchyCompletionFunctorPacket_multiplication_laws [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      firstBind secondBind composite : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont regular sealRow firstBind ->
        Cont firstBind monadRow secondBind ->
          Cont secondBind universal composite ->
            PkgSig bundle composite pkg ->
              UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory monadRow ∧
                UnaryHistory universal ∧ UnaryHistory firstBind ∧ UnaryHistory secondBind ∧
                  UnaryHistory composite ∧ Cont regular sealRow firstBind ∧
                    Cont firstBind monadRow secondBind ∧ Cont secondBind universal composite ∧
                      Cont monadRow universal endpoint ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle composite pkg := by
  intro packet regularSealFirst firstMonadSecond secondUniversalComposite compositePkg
  obtain ⟨_metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, _metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have firstUnary : UnaryHistory firstBind :=
    unary_cont_closed regularUnary sealUnary regularSealFirst
  have secondUnary : UnaryHistory secondBind :=
    unary_cont_closed firstUnary monadUnary firstMonadSecond
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed secondUnary universalUnary secondUniversalComposite
  exact
    ⟨regularUnary,
      sealUnary,
      monadUnary,
      universalUnary,
      firstUnary,
      secondUnary,
      compositeUnary,
      regularSealFirst,
      firstMonadSecond,
      secondUniversalComposite,
      monadUniversalEndpoint,
      endpointPkg,
      compositePkg⟩

theorem CauchyCompletionFunctorPacket_ledger_exactness [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont endpoint classifier exported ->
        PkgSig bundle exported pkg ->
          UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
            UnaryHistory monadRow ∧ UnaryHistory universal ∧ UnaryHistory classifier ∧
              UnaryHistory transport ∧ UnaryHistory nameCert ∧ UnaryHistory endpoint ∧
                UnaryHistory exported ∧ Cont metric regular sealRow ∧
                  Cont monadRow universal endpoint ∧ Cont endpoint classifier exported ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle exported pkg := by
  intro packet endpointClassifierExported exportedPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, classifierUnary,
    transportUnary, nameCertUnary, endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed endpointUnary classifierUnary endpointClassifierExported
  exact
    ⟨metricUnary,
      regularUnary,
      sealUnary,
      monadUnary,
      universalUnary,
      classifierUnary,
      transportUnary,
      nameCertUnary,
      endpointUnary,
      exportedUnary,
      metricRegularSeal,
      monadUniversalEndpoint,
      endpointClassifierExported,
      endpointPkg,
      exportedPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
