import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Ask
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Package
open BEDC.FKernel.NameCert

theorem CauchyCompletionLeftExactnessNameCertObligations
    {S U D K E H C P N sourceUnit denseKernel extension route : BHist} :
    UnaryHistory S ->
      UnaryHistory U ->
        UnaryHistory D ->
          UnaryHistory K ->
            UnaryHistory E ->
              Cont S U sourceUnit ->
                Cont D K denseKernel ->
                  Cont sourceUnit denseKernel extension ->
                    Cont extension E route ->
                      UnaryHistory sourceUnit ∧
                        UnaryHistory denseKernel ∧
                          UnaryHistory extension ∧
                            UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary unitUnary denseUnary kernelUnary extensionUnary
    sourceUnitRoute denseKernelRoute extensionRoute replayRoute
  have sourceUnitUnary : UnaryHistory sourceUnit :=
    unary_cont_closed sourceUnary unitUnary sourceUnitRoute
  have denseKernelUnary : UnaryHistory denseKernel :=
    unary_cont_closed denseUnary kernelUnary denseKernelRoute
  have extensionUnary' : UnaryHistory extension :=
    unary_cont_closed sourceUnitUnary denseKernelUnary extensionRoute
  have routeUnary : UnaryHistory route :=
    unary_cont_closed extensionUnary' extensionUnary replayRoute
  exact ⟨sourceUnitUnary, denseKernelUnary, extensionUnary', routeUnary⟩

theorem CauchyModulusSpaceFiniteRoute [AskSetup] [PackageSetup]
    {index schedule stream dyadic readback realSeal transport replay provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory index ->
      UnaryHistory schedule ->
        UnaryHistory stream ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory realSeal ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    UnaryHistory provenance ->
                      UnaryHistory localName ->
                        Cont index schedule stream ->
                          Cont dyadic readback realSeal ->
                            Cont transport replay provenance ->
                              Cont stream realSeal route ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle localName pkg ->
                                    UnaryHistory route ∧ Cont stream realSeal route ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro _indexUnary _scheduleUnary streamUnary _dyadicUnary _readbackUnary realSealUnary
    _transportUnary _replayUnary _provenanceUnary _localNameUnary _indexScheduleStream
    _dyadicReadbackRealSeal _transportReplayProvenance streamRealSealRoute provenancePkg
    localNamePkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed streamUnary realSealUnary streamRealSealRoute
  exact ⟨routeUnary, streamRealSealRoute, provenancePkg, localNamePkg⟩

theorem CauchySeedRealSealBoundary {W D R E toleranceRead readbackRead sealRead : BHist} :
    UnaryHistory W →
      UnaryHistory D →
        UnaryHistory R →
          UnaryHistory E →
            Cont W D toleranceRead →
              Cont toleranceRead R readbackRead →
                Cont readbackRead E sealRead →
                  UnaryHistory toleranceRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealRead ∧ Cont W D toleranceRead ∧
                      Cont toleranceRead R readbackRead ∧ Cont readbackRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowUnary toleranceUnary readbackUnary sealUnary windowToleranceRead
    toleranceReadbackRead readbackSealRead
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary toleranceUnary windowToleranceRead
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary readbackUnary toleranceReadbackRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary readbackSealRead
  exact
    ⟨toleranceReadUnary, readbackReadUnary, sealReadUnary, windowToleranceRead,
      toleranceReadbackRead, readbackSealRead⟩

def CauchyModulusSpaceCarrier (I S W D R Q H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory I ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N

theorem CauchyModulusSpaceNameCertObligations [AskSetup] [PackageSetup]
    {I S W D R Q H C P N schedule readback route : BHist} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N ->
      Cont S W schedule ->
        Cont D R readback ->
          Cont schedule readback route ->
            UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro carrier scheduleCont readbackCont routeCont
  obtain ⟨_iUnary, sUnary, wUnary, dUnary, rUnary, _qUnary, _hUnary, _cUnary,
    _pUnary, _nUnary⟩ := carrier
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed sUnary wUnary scheduleCont
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed dUnary rUnary readbackCont
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary readbackUnary routeCont
  exact ⟨scheduleUnary, readbackUnary, routeUnary⟩

theorem CauchyModulusSpaceSeedInterface [AskSetup] [PackageSetup]
    {I S W D R Q H C P N scheduleRead toleranceRead readbackRead sealRead structuralRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N ->
      Cont I S scheduleRead ->
        Cont scheduleRead D toleranceRead ->
          Cont toleranceRead R readbackRead ->
            Cont readbackRead Q sealRead ->
              Cont H C structuralRead ->
                Cont P N namedRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row I ∨ hsame row S ∨ hsame row D ∨ hsame row R ∨
                              hsame row Q ∨ hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory scheduleRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                            UnaryHistory structuralRead ∧ UnaryHistory namedRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier scheduleRoute toleranceRoute readbackRoute sealRoute structuralRoute namingRoute
    provenancePkg namePkg
  obtain ⟨iUnary, sUnary, _wUnary, dUnary, rUnary, qUnary, hUnary, cUnary, pUnary,
    nUnary⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed iUnary sUnary scheduleRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed scheduleReadUnary dUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary qUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namingRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  · exact
      ⟨scheduleReadUnary, toleranceReadUnary, readbackReadUnary, sealReadUnary,
        structuralReadUnary, namedReadUnary, provenancePkg, namePkg⟩

theorem CauchySeedCarrierBoundary
    {S W D R E H C P N window tolerance readback sealRow transport replay provenance
      nameRoute : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont S W window ->
                        Cont window D tolerance ->
                          Cont tolerance R readback ->
                            Cont readback E sealRow ->
                              Cont sealRow H transport ->
                                Cont transport C replay ->
                                  Cont replay P provenance ->
                                    Cont provenance N nameRoute ->
                                      UnaryHistory window ∧
                                        UnaryHistory tolerance ∧
                                          UnaryHistory readback ∧
                                            UnaryHistory sealRow ∧
                                              UnaryHistory transport ∧
                                                UnaryHistory replay ∧
                                                  UnaryHistory provenance ∧
                                                    UnaryHistory nameRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary windowUnary toleranceUnary readbackUnary sealUnary transportUnary replayUnary
    provenanceUnary nameUnary sourceWindow windowTolerance toleranceReadback readbackSeal
    sealTransport transportReplay replayProvenance provenanceName
  have windowClosed : UnaryHistory window :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have toleranceClosed : UnaryHistory tolerance :=
    unary_cont_closed windowClosed toleranceUnary windowTolerance
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed toleranceClosed readbackUnary toleranceReadback
  have sealClosed : UnaryHistory sealRow :=
    unary_cont_closed readbackClosed sealUnary readbackSeal
  have transportClosed : UnaryHistory transport :=
    unary_cont_closed sealClosed transportUnary sealTransport
  have replayClosed : UnaryHistory replay :=
    unary_cont_closed transportClosed replayUnary transportReplay
  have provenanceClosed : UnaryHistory provenance :=
    unary_cont_closed replayClosed provenanceUnary replayProvenance
  have nameClosed : UnaryHistory nameRoute :=
    unary_cont_closed provenanceClosed nameUnary provenanceName
  exact
    ⟨windowClosed, toleranceClosed, readbackClosed, sealClosed, transportClosed, replayClosed,
      provenanceClosed, nameClosed⟩

theorem CauchySeedNameCertObligation [AskSetup] [PackageSetup]
    {S W D R E H C P N window tolerance readback sealRow transport replay provenance
      nameRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont S W window →
                        Cont window D tolerance →
                          Cont tolerance R readback →
                            Cont readback E sealRow →
                              Cont sealRow H transport →
                                Cont transport C replay →
                                  Cont replay P provenance →
                                    Cont provenance N nameRoute →
                                      PkgSig bundle P pkg →
                                        PkgSig bundle N pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row nameRoute ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row sealRow ∨ hsame row transport ∨
                                                  hsame row replay ∨ hsame row provenance ∨
                                                    hsame row nameRoute)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory window ∧ UnaryHistory tolerance ∧
                                              UnaryHistory readback ∧ UnaryHistory sealRow ∧
                                                UnaryHistory transport ∧ UnaryHistory replay ∧
                                                  UnaryHistory provenance ∧
                                                    UnaryHistory nameRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary windowUnary toleranceUnary readbackUnary sealUnary transportUnary replayUnary
    provenanceUnary nameUnary sourceWindow windowTolerance toleranceReadback readbackSeal
    sealTransport transportReplay replayProvenance provenanceName provenancePkg namePkg
  have windowClosed : UnaryHistory window :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have toleranceClosed : UnaryHistory tolerance :=
    unary_cont_closed windowClosed toleranceUnary windowTolerance
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed toleranceClosed readbackUnary toleranceReadback
  have sealClosed : UnaryHistory sealRow :=
    unary_cont_closed readbackClosed sealUnary readbackSeal
  have transportClosed : UnaryHistory transport :=
    unary_cont_closed sealClosed transportUnary sealTransport
  have replayClosed : UnaryHistory replay :=
    unary_cont_closed transportClosed replayUnary transportReplay
  have provenanceClosed : UnaryHistory provenance :=
    unary_cont_closed replayClosed provenanceUnary replayProvenance
  have nameClosed : UnaryHistory nameRoute :=
    unary_cont_closed provenanceClosed nameUnary provenanceName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealRow ∨ hsame row transport ∨ hsame row replay ∨
              hsame row provenance ∨ hsame row nameRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRoute ⟨hsame_refl nameRoute, nameClosed⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, windowClosed, toleranceClosed, readbackClosed, sealClosed, transportClosed,
      replayClosed, provenanceClosed, nameClosed⟩

theorem CauchyRootUnaryAdmission [AskSetup] [PackageSetup]
    {stream request dyadic readback realSeal _transport _replay _provenance _localName tailRead
      toleranceRead realRead : BHist} :
    UnaryHistory stream -> UnaryHistory request -> UnaryHistory dyadic ->
      UnaryHistory readback -> UnaryHistory realSeal -> Cont stream request tailRead ->
        Cont tailRead dyadic toleranceRead -> Cont toleranceRead readback realRead ->
          UnaryHistory tailRead ∧ UnaryHistory toleranceRead ∧ UnaryHistory realRead ∧
            Cont stream request tailRead ∧ Cont tailRead dyadic toleranceRead ∧
              Cont toleranceRead readback realRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro streamUnary requestUnary dyadicUnary readbackUnary _realSealUnary tailRoute
    toleranceRoute realRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed streamUnary requestUnary tailRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailReadUnary dyadicUnary toleranceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceReadUnary readbackUnary realRoute
  exact
    ⟨tailReadUnary, toleranceReadUnary, realReadUnary, tailRoute, toleranceRoute,
      realRoute⟩

theorem CauchyRootFilterModulusCompatibility
    {S Q D R E H C P N streamRequest toleranceRead readbackRead sealRead
      structuralRead namedRead : BHist} :
    UnaryHistory S ->
      UnaryHistory Q ->
        UnaryHistory D ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont S Q streamRequest ->
                        Cont streamRequest D toleranceRead ->
                          Cont toleranceRead R readbackRead ->
                            Cont readbackRead E sealRead ->
                              Cont H C structuralRead ->
                                Cont P N namedRead ->
                                  UnaryHistory streamRequest ∧
                                    UnaryHistory toleranceRead ∧
                                      UnaryHistory readbackRead ∧
                                        UnaryHistory sealRead ∧
                                          UnaryHistory structuralRead ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary qUnary dUnary rUnary eUnary hUnary cUnary pUnary nUnary streamRoute
    toleranceRoute readbackRoute sealRoute structuralRoute namingRoute
  have streamRequestUnary : UnaryHistory streamRequest :=
    unary_cont_closed sUnary qUnary streamRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamRequestUnary dUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary eUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namingRoute
  exact
    ⟨streamRequestUnary, toleranceReadUnary, readbackReadUnary, sealReadUnary,
      structuralReadUnary, namedReadUnary⟩

theorem CauchyRootRegSeqRatRealHandoff [AskSetup] [PackageSetup]
    {stream request dyadic readback realSeal transport replay provenance localName
      requestRead toleranceRead rationalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory request ->
        UnaryHistory dyadic ->
          UnaryHistory readback ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont stream request requestRead ->
                    Cont requestRead dyadic toleranceRead ->
                      Cont toleranceRead readback rationalRead ->
                        Cont rationalRead realSeal sealRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row stream ∨ hsame row request ∨
                                      hsame row dyadic ∨ hsame row readback ∨
                                        hsame row realSeal ∨ hsame row sealRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory requestRead ∧ UnaryHistory toleranceRead ∧
                                  UnaryHistory rationalRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro streamUnary requestUnary dyadicUnary readbackUnary realSealUnary _transportUnary
    _replayUnary streamRequest toleranceRoute rationalRoute sealRoute provenancePkg localNamePkg
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed streamUnary requestUnary streamRequest
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed requestReadUnary dyadicUnary toleranceRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed toleranceReadUnary readbackUnary rationalRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalReadUnary realSealUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  · exact ⟨requestReadUnary, toleranceReadUnary, rationalReadUnary, sealReadUnary⟩

end BEDC.Derived.CauchyUp
