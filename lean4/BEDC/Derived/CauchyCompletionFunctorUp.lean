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

theorem CauchyCompletionFunctorPacket_source_metric_unit_handoff [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      unitRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont metric sealRow unitRead ->
        Cont unitRead transport handoff ->
          PkgSig bundle handoff pkg ->
            UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
              UnaryHistory monadRow ∧ UnaryHistory transport ∧ UnaryHistory nameCert ∧
                UnaryHistory unitRead ∧ UnaryHistory handoff ∧ Cont metric regular sealRow ∧
                  Cont metric sealRow unitRead ∧ Cont unitRead transport handoff ∧
                    Cont classifier transport nameCert ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet metricSealUnit unitTransportHandoff handoffPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, _universalUnary,
    _classifierUnary, transportUnary, nameCertUnary, _endpointUnary, metricRegularSeal,
    _monadUniversalEndpoint, classifierTransportNameCert, endpointPkg⟩ := packet
  have unitReadUnary : UnaryHistory unitRead :=
    unary_cont_closed metricUnary sealUnary metricSealUnit
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unitReadUnary transportUnary unitTransportHandoff
  exact
    ⟨metricUnary, regularUnary, sealUnary, monadUnary, transportUnary, nameCertUnary,
      unitReadUnary, handoffUnary, metricRegularSeal, metricSealUnit, unitTransportHandoff,
      classifierTransportNameCert, endpointPkg, handoffPkg⟩

theorem CauchyCompletionFunctorPacket_universal_property_extension_exactness
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont sealRow monadRow extensionRead ->
        PkgSig bundle extensionRead pkg ->
          UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
            UnaryHistory monadRow ∧ UnaryHistory universal ∧ UnaryHistory extensionRead ∧
              Cont metric regular sealRow ∧ Cont sealRow monadRow extensionRead ∧
                Cont monadRow universal endpoint ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle extensionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sealMonadExtension extensionPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sealUnary monadUnary sealMonadExtension
  exact
    ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, extensionUnary,
      metricRegularSeal, sealMonadExtension, monadUniversalEndpoint, endpointPkg, extensionPkg⟩

theorem CauchyCompletionFunctorPacket_completion_consumer_handoff [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont sealRow monadRow completionRead ->
        PkgSig bundle completionRead pkg ->
          UnaryHistory sealRow ∧ UnaryHistory monadRow ∧ UnaryHistory universal ∧
            UnaryHistory completionRead ∧ Cont sealRow monadRow completionRead ∧
              Cont monadRow universal endpoint ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet sealMonadCompletion completionPkg
  obtain ⟨_metricUnary, _regularUnary, sealUnary, monadUnary, universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, _metricRegularSeal,
    monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary monadUnary sealMonadCompletion
  exact
    ⟨sealUnary, monadUnary, universalUnary, completionUnary, sealMonadCompletion,
      monadUniversalEndpoint, endpointPkg, completionPkg⟩

theorem CauchyCompletionFunctorPacket_bind_ledger_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint bindRead
      extensionRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont regular sealRow bindRead ->
        Cont bindRead universal extensionRead ->
          Cont extensionRead classifier exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory universal ∧
                UnaryHistory classifier ∧ UnaryHistory bindRead ∧ UnaryHistory extensionRead ∧
                  UnaryHistory exported ∧ Cont regular sealRow bindRead ∧
                    Cont bindRead universal extensionRead ∧
                      Cont extensionRead classifier exported ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet regularSealBind bindUniversalExtension extensionClassifierExported exportedPkg
  obtain ⟨_metricUnary, regularUnary, sealUnary, _monadUnary, universalUnary,
    classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, _metricRegularSeal,
    _monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have bindUnary : UnaryHistory bindRead :=
    unary_cont_closed regularUnary sealUnary regularSealBind
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed bindUnary universalUnary bindUniversalExtension
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed extensionUnary classifierUnary extensionClassifierExported
  exact
    ⟨regularUnary, sealUnary, universalUnary, classifierUnary, bindUnary, extensionUnary,
      exportedUnary, regularSealBind, bindUniversalExtension, extensionClassifierExported,
      endpointPkg, exportedPkg⟩

theorem CauchyCompletionFunctorPacket_obligation_closure_package [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint unitRead
      bindRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont metric sealRow unitRead ->
        Cont regular monadRow bindRead ->
          PkgSig bundle unitRead pkg ->
            PkgSig bundle bindRead pkg ->
              UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
                UnaryHistory monadRow ∧ UnaryHistory universal ∧ UnaryHistory unitRead ∧
                  UnaryHistory bindRead ∧ Cont metric regular sealRow ∧
                    Cont monadRow universal endpoint ∧ Cont metric sealRow unitRead ∧
                      Cont regular monadRow bindRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle unitRead pkg ∧ PkgSig bundle bindRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet metricSealUnit regularMonadBind unitPkg bindPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have unitReadUnary : UnaryHistory unitRead :=
    unary_cont_closed metricUnary sealUnary metricSealUnit
  have bindReadUnary : UnaryHistory bindRead :=
    unary_cont_closed regularUnary monadUnary regularMonadBind
  exact
    ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, unitReadUnary,
      bindReadUnary, metricRegularSeal, monadUniversalEndpoint, metricSealUnit,
      regularMonadBind, endpointPkg, unitPkg, bindPkg⟩

theorem CauchyCompletionFunctorPacket_public_completion_export [AskSetup] [PackageSetup]
    {M R S U B E P T N consumerRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket M R S U B E P T N bundle pkg ->
      Cont S U consumerRead ->
        Cont consumerRead N exportRead ->
          PkgSig bundle exportRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row S ∧ CauchyCompletionFunctorPacket M R S U B E P T N bundle pkg)
                (fun row : BHist =>
                  hsame row S ∧ Cont S U consumerRead ∧ Cont consumerRead N exportRead)
                (fun row : BHist => hsame row S ∧ PkgSig bundle exportRead pkg)
                hsame ∧
              UnaryHistory consumerRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet sealConsumer consumerExport exportPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary,
    classifierUnary, transportUnary, nameCertUnary, endpointUnary, metricRegularSeal,
    monadUniversalEndpoint, classifierTransportNameCert, endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary monadUnary sealConsumer
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed consumerUnary endpointUnary consumerExport
  have packetWitness :
      CauchyCompletionFunctorPacket M R S U B E P T N bundle pkg := by
    exact
      ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, classifierUnary,
        transportUnary, nameCertUnary, endpointUnary, metricRegularSeal, monadUniversalEndpoint,
        classifierTransportNameCert, endpointPkg⟩
  have sourceSeal :
      (fun row : BHist =>
        hsame row S ∧ CauchyCompletionFunctorPacket M R S U B E P T N bundle pkg) S := by
    exact ⟨hsame_refl S, packetWitness⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row S ∧ CauchyCompletionFunctorPacket M R S U B E P T N bundle pkg)
          (fun row : BHist =>
            hsame row S ∧ Cont S U consumerRead ∧ Cont consumerRead N exportRead)
          (fun row : BHist => hsame row S ∧ PkgSig bundle exportRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro S sourceSeal
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
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, sealConsumer, consumerExport⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact ⟨cert, consumerUnary, exportUnary⟩

theorem CauchyCompletionFunctorPacket_observation_budget_factorization
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint obsStart
      obsWindow obsDyadic obsRat obsSeal routedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      UnaryHistory obsStart ->
        UnaryHistory obsWindow ->
          UnaryHistory obsRat ->
            Cont obsStart obsWindow obsDyadic ->
              Cont obsDyadic obsRat obsSeal ->
                Cont obsSeal sealRow routedSeal ->
                  PkgSig bundle routedSeal pkg ->
                    UnaryHistory obsDyadic ∧ UnaryHistory obsSeal ∧
                      UnaryHistory routedSeal ∧ Cont metric regular sealRow ∧
                        Cont obsStart obsWindow obsDyadic ∧ Cont obsDyadic obsRat obsSeal ∧
                          Cont obsSeal sealRow routedSeal ∧
                            Cont monadRow universal endpoint ∧ PkgSig bundle endpoint pkg ∧
                              PkgSig bundle routedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet obsStartUnary obsWindowUnary obsRatUnary obsStartObsWindowObsDyadic
    obsDyadicObsRatObsSeal obsSealSealRowRoutedSeal routedSealPkg
  obtain ⟨_metricUnary, _regularUnary, sealUnary, _monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal,
    monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have obsDyadicUnary : UnaryHistory obsDyadic :=
    unary_cont_closed obsStartUnary obsWindowUnary obsStartObsWindowObsDyadic
  have obsSealUnary : UnaryHistory obsSeal :=
    unary_cont_closed obsDyadicUnary obsRatUnary obsDyadicObsRatObsSeal
  have routedSealUnary : UnaryHistory routedSeal :=
    unary_cont_closed obsSealUnary sealUnary obsSealSealRowRoutedSeal
  exact
    ⟨obsDyadicUnary, obsSealUnary, routedSealUnary, metricRegularSeal,
      obsStartObsWindowObsDyadic, obsDyadicObsRatObsSeal, obsSealSealRowRoutedSeal,
      monadUniversalEndpoint, endpointPkg, routedSealPkg⟩

theorem CauchyCompletionFunctorPacket_finite_observation_selector_factorization
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      selectorStart selectorWindow selectorDyadic selectorRat selectorExit selectorRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      UnaryHistory selectorStart ->
        UnaryHistory selectorWindow ->
          UnaryHistory selectorRat ->
            UnaryHistory selectorExit ->
              Cont selectorStart selectorWindow selectorDyadic ->
                Cont selectorDyadic selectorRat selectorExit ->
                  Cont selectorExit sealRow selectorRead ->
                    Cont selectorRead monadRow completionRead ->
                      PkgSig bundle completionRead pkg ->
                        UnaryHistory selectorDyadic ∧ UnaryHistory selectorRead ∧
                          UnaryHistory completionRead ∧
                            Cont selectorStart selectorWindow selectorDyadic ∧
                              Cont selectorDyadic selectorRat selectorExit ∧
                                Cont selectorExit sealRow selectorRead ∧
                                  Cont selectorRead monadRow completionRead ∧
                                    Cont monadRow universal endpoint ∧
                                      PkgSig bundle endpoint pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet selectorStartUnary selectorWindowUnary selectorRatUnary selectorExitUnary
    selectorStartSelectorWindowSelectorDyadic selectorDyadicSelectorRatSelectorExit
    selectorExitSealRowSelectorRead selectorReadMonadRowCompletionRead completionReadPkg
  obtain ⟨_metricUnary, _regularUnary, sealUnary, monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, _metricRegularSeal,
    monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have selectorDyadicUnary : UnaryHistory selectorDyadic :=
    unary_cont_closed selectorStartUnary selectorWindowUnary
      selectorStartSelectorWindowSelectorDyadic
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed selectorExitUnary sealUnary selectorExitSealRowSelectorRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed selectorReadUnary monadUnary selectorReadMonadRowCompletionRead
  exact
    ⟨selectorDyadicUnary, selectorReadUnary, completionReadUnary,
      selectorStartSelectorWindowSelectorDyadic, selectorDyadicSelectorRatSelectorExit,
      selectorExitSealRowSelectorRead, selectorReadMonadRowCompletionRead, monadUniversalEndpoint,
      endpointPkg, completionReadPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
