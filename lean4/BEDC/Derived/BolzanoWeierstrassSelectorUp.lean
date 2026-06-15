import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Derived.BolzanoWeierstrassSelectorUp.NestedIntervalObligation
import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorClusterRoute (x : BolzanoWeierstrassSelectorUp) :
    (exists boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
        regularHandoff realSeal transport route provenance name : BHist,
        x =
          BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
            selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
          bolzanoWeierstrassSelectorFields x =
            [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
              regularHandoff, realSeal, transport, route, provenance, name] ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist selectedWindow) =
            selectedWindow ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist dyadicLedger) =
            dyadicLedger ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist regularHandoff) =
            regularHandoff ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist realSeal) =
            realSeal) ∧
      bolzanoWeierstrassSelectorEncodeBHist (BHist.e1 (BHist.e1 BHist.Empty)) =
        [BMark.b1, BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  have decodeEncode :
      ∀ h : BHist,
        bolzanoWeierstrassSelectorDecodeBHist
            (bolzanoWeierstrassSelectorEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
      regularHandoff realSeal transport route provenance name =>
      constructor
      · exact
          ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl,
            decodeEncode selectedWindow, decodeEncode dyadicLedger, decodeEncode regularHandoff,
            decodeEncode realSeal⟩
      · rfl

theorem BolzanoWeierstrassSelectorFiniteWindowInduction
    (x : BolzanoWeierstrassSelectorUp) :
    ∃ boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name : BHist,
      x =
        BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
          selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
        bolzanoWeierstrassSelectorFields x =
          [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name] ∧
          hsame transport transport ∧
            bolzanoWeierstrassSelectorDecodeBHist
                (bolzanoWeierstrassSelectorEncodeBHist selectedWindow) =
              selectedWindow ∧
              bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist realSeal) =
                realSeal := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  have decodeEncode :
      ∀ h : BHist,
        bolzanoWeierstrassSelectorDecodeBHist
            (bolzanoWeierstrassSelectorEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name =>
      exact
        ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
          regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl,
          hsame_refl transport, decodeEncode selectedWindow, decodeEncode realSeal⟩

theorem BolzanoWeierstrassSelectorFiniteMonotoneInduction
    {boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name inductionStep : BHist} :
    Cont boundedWindow monotoneSelector selectedWindow ->
      Cont selectedWindow cofinalEvidence inductionStep ->
        UnaryHistory boundedWindow ->
          UnaryHistory monotoneSelector ->
            UnaryHistory cofinalEvidence ->
              UnaryHistory selectedWindow ∧ UnaryHistory inductionStep ∧
                Cont boundedWindow monotoneSelector selectedWindow ∧
                  Cont selectedWindow cofinalEvidence inductionStep ∧
                    bolzanoWeierstrassSelectorFields
                        (BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector
                          cofinalEvidence selectedWindow dyadicLedger regularHandoff realSeal
                          transport route provenance name) =
                      [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow,
                        dyadicLedger, regularHandoff, realSeal, transport, route, provenance,
                        name] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute inductionRoute boundedUnary selectorUnary cofinalUnary
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed boundedUnary selectorUnary selectedRoute
  have inductionUnary : UnaryHistory inductionStep :=
    unary_cont_closed selectedUnary cofinalUnary inductionRoute
  exact ⟨selectedUnary, inductionUnary, selectedRoute, inductionRoute, rfl⟩

theorem BolzanoWeierstrassSelectorNonescape (x : BolzanoWeierstrassSelectorUp) :
    (exists boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
        regularHandoff realSeal transport route provenance name : BHist,
        x =
          BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
            selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
          bolzanoWeierstrassSelectorFields x =
            [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
              regularHandoff, realSeal, transport, route, provenance, name] ∧
          bolzanoWeierstrassSelectorFromEventFlow
              (bolzanoWeierstrassSelectorToEventFlow x) =
            some x ∧
          hsame transport transport ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist realSeal) =
            realSeal) ∧
      bolzanoWeierstrassSelectorEncodeBHist (BHist.e1 (BHist.e1 (BHist.e0 BHist.Empty))) =
        [BMark.b1, BMark.b1, BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark hsame BHistCarrier ChapterTasteGate
  have decodeEncode :
      ∀ h : BHist,
        bolzanoWeierstrassSelectorDecodeBHist
            (bolzanoWeierstrassSelectorEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name =>
      have roundTrip :
          bolzanoWeierstrassSelectorFromEventFlow
              (bolzanoWeierstrassSelectorToEventFlow
                (BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector
                  cofinalEvidence selectedWindow dyadicLedger regularHandoff realSeal transport
                  route provenance name)) =
            some
              (BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
                selectedWindow dyadicLedger regularHandoff realSeal transport route provenance
                name) := by
        change
          some
              (BolzanoWeierstrassSelectorUp.mk
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist boundedWindow))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist monotoneSelector))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist cofinalEvidence))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist selectedWindow))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist dyadicLedger))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist regularHandoff))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist realSeal))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist transport))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist route))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist provenance))
                (bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist name))) =
            some
              (BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
                selectedWindow dyadicLedger regularHandoff realSeal transport route provenance
                name)
        rw [decodeEncode boundedWindow, decodeEncode monotoneSelector,
          decodeEncode cofinalEvidence, decodeEncode selectedWindow, decodeEncode dyadicLedger,
          decodeEncode regularHandoff, decodeEncode realSeal, decodeEncode transport,
          decodeEncode route, decodeEncode provenance, decodeEncode name]
      constructor
      · exact
          ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl, roundTrip,
            hsame_refl transport, decodeEncode realSeal⟩
      · rfl

theorem BolzanoWeierstrassSelectorFiniteSubsequenceObligations
    {B M Q W D R E H C P N finiteRead regularRead sealRead : BHist} :
    Cont B M W ->
      Cont W D finiteRead ->
        Cont finiteRead R regularRead ->
          Cont regularRead E sealRead ->
            UnaryHistory B ->
              UnaryHistory M ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    UnaryHistory E ->
                      UnaryHistory W ∧ UnaryHistory finiteRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ Cont B M W ∧
                          Cont W D finiteRead ∧ Cont finiteRead R regularRead ∧
                            Cont regularRead E sealRead ∧
                              bolzanoWeierstrassSelectorFields
                                  (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                                [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute finiteRoute regularRoute sealRoute bUnary mUnary dUnary rUnary eUnary
  have selectedUnary : UnaryHistory W :=
    unary_cont_closed bUnary mUnary selectedRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed selectedUnary dUnary finiteRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed finiteUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  exact
    ⟨selectedUnary, finiteUnary, regularUnary, sealUnary, selectedRoute, finiteRoute,
      regularRoute, sealRoute, rfl⟩

theorem BolzanoWeierstrassSelectorFiniteWindowStabilization
    {boundedWindow monotoneSelector cofinalEvidence selectedWindow laterWindow dyadicLedger
      regularHandoff realSeal transport route provenance name stabilizedRead : BHist} :
    Cont boundedWindow monotoneSelector selectedWindow →
      Cont boundedWindow monotoneSelector laterWindow →
        Cont laterWindow dyadicLedger regularHandoff →
          Cont regularHandoff realSeal stabilizedRead →
            UnaryHistory boundedWindow →
              UnaryHistory monotoneSelector →
                UnaryHistory dyadicLedger →
                  UnaryHistory realSeal →
                    UnaryHistory laterWindow ∧ UnaryHistory regularHandoff ∧
                      UnaryHistory stabilizedRead ∧
                        Cont boundedWindow monotoneSelector laterWindow ∧
                          Cont laterWindow dyadicLedger regularHandoff ∧
                            Cont regularHandoff realSeal stabilizedRead ∧
                              bolzanoWeierstrassSelectorFields
                                  (BolzanoWeierstrassSelectorUp.mk boundedWindow
                                    monotoneSelector cofinalEvidence selectedWindow
                                    dyadicLedger regularHandoff realSeal transport route
                                    provenance name) =
                                [boundedWindow, monotoneSelector, cofinalEvidence,
                                  selectedWindow, dyadicLedger, regularHandoff, realSeal,
                                  transport, route, provenance, name] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro _selectedRoute laterRoute handoffRoute sealRoute boundedUnary selectorUnary
    dyadicUnary realUnary
  have laterUnary : UnaryHistory laterWindow :=
    unary_cont_closed boundedUnary selectorUnary laterRoute
  have handoffUnary : UnaryHistory regularHandoff :=
    unary_cont_closed laterUnary dyadicUnary handoffRoute
  have stabilizedUnary : UnaryHistory stabilizedRead :=
    unary_cont_closed handoffUnary realUnary sealRoute
  exact
    ⟨laterUnary, handoffUnary, stabilizedUnary, laterRoute, handoffRoute, sealRoute, rfl⟩

theorem BolzanoWeierstrassSelectorRegSeqRatReadbackNonescape
    {B M Q W D R E H C P N selectedRead dyadicRead regSeqRead realSeal : BHist} :
    Cont B M selectedRead ->
      Cont selectedRead Q W ->
        Cont W D dyadicRead ->
          Cont dyadicRead R regSeqRead ->
            Cont regSeqRead E realSeal ->
              UnaryHistory B ->
                UnaryHistory M ->
                  UnaryHistory Q ->
                    UnaryHistory D ->
                      UnaryHistory R ->
                        UnaryHistory E ->
                          UnaryHistory selectedRead ∧ UnaryHistory W ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory regSeqRead ∧
                              UnaryHistory realSeal ∧ Cont B M selectedRead ∧
                                Cont selectedRead Q W ∧ Cont W D dyadicRead ∧
                                  Cont dyadicRead R regSeqRead ∧ Cont regSeqRead E realSeal ∧
                                    bolzanoWeierstrassSelectorFields
                                        (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C
                                          P N) =
                                      [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute windowRoute dyadicRoute regSeqRoute sealRoute bUnary mUnary qUnary
    dUnary rUnary eUnary
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed bUnary mUnary selectedRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary qUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed dyadicUnary rUnary regSeqRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqUnary eUnary sealRoute
  exact
    ⟨selectedUnary, windowUnary, dyadicUnary, regSeqUnary, sealUnary, selectedRoute,
      windowRoute, dyadicRoute, regSeqRoute, sealRoute, rfl⟩

theorem BolzanoWeierstrassSelectorRegularCauchyClusterSeal
    {B M Q W D R E H C P N selected regular sealRead clusterRead : BHist} :
    Cont B M selected →
      Cont selected D regular →
        Cont regular R sealRead →
          Cont sealRead E clusterRead →
            UnaryHistory B →
              UnaryHistory M →
                UnaryHistory D →
                  UnaryHistory R →
                    UnaryHistory E →
                      bolzanoWeierstrassSelectorFields
                            (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                          [B, M, Q, W, D, R, E, H, C, P, N] ∧
                        UnaryHistory selected ∧ UnaryHistory regular ∧
                          UnaryHistory sealRead ∧ UnaryHistory clusterRead ∧
                            Cont selected D regular ∧ Cont regular R sealRead ∧
                              Cont sealRead E clusterRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute regularRoute sealRoute clusterRoute bUnary mUnary dUnary rUnary eUnary
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed bUnary mUnary selectedRoute
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed selectedUnary dUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary rUnary sealRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed sealUnary eUnary clusterRoute
  exact
    ⟨rfl, selectedUnary, regularUnary, sealUnary, clusterUnary, regularRoute, sealRoute,
      clusterRoute⟩

theorem BolzanoWeierstrassSelectorBoundedSubsequenceCarrier
    {B M Q W D R E H C P N selectedRead inspectedRead : BHist} :
    Cont B M selectedRead ->
      Cont selectedRead Q inspectedRead ->
        UnaryHistory B ->
          UnaryHistory M ->
            UnaryHistory Q ->
              UnaryHistory selectedRead ∧ UnaryHistory inspectedRead ∧
                Cont B M selectedRead ∧ Cont selectedRead Q inspectedRead ∧
                  bolzanoWeierstrassSelectorFields
                      (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                    [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute inspectedRoute bUnary mUnary qUnary
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed bUnary mUnary selectedRoute
  have inspectedUnary : UnaryHistory inspectedRead :=
    unary_cont_closed selectedUnary qUnary inspectedRoute
  exact ⟨selectedUnary, inspectedUnary, selectedRoute, inspectedRoute, rfl⟩

theorem BolzanoWeierstrassSelectorDyadicWindowObligation
    {B M Q W D R E H C P N selectedRead dyadicRead : BHist} :
    Cont B M selectedRead ->
      Cont selectedRead D dyadicRead ->
        UnaryHistory B ->
          UnaryHistory M ->
            UnaryHistory D ->
              UnaryHistory selectedRead ∧ UnaryHistory dyadicRead ∧
                Cont B M selectedRead ∧ Cont selectedRead D dyadicRead ∧
                  bolzanoWeierstrassSelectorFields
                      (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                    [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute dyadicRoute bUnary mUnary dUnary
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed bUnary mUnary selectedRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed selectedUnary dUnary dyadicRoute
  exact ⟨selectedUnary, dyadicUnary, selectedRoute, dyadicRoute, rfl⟩

theorem BolzanoWeierstrassSelectorRealSealFinality
    {B M Q W D R E H C P N selectedRead dyadicRead regularRead sealRead : BHist} :
    Cont B M selectedRead ->
      Cont selectedRead D dyadicRead ->
        Cont dyadicRead R regularRead ->
          Cont regularRead E sealRead ->
            UnaryHistory B ->
              UnaryHistory M ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    UnaryHistory E ->
                      UnaryHistory selectedRead ∧ UnaryHistory dyadicRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                          Cont B M selectedRead ∧ Cont selectedRead D dyadicRead ∧
                            Cont dyadicRead R regularRead ∧ Cont regularRead E sealRead ∧
                              bolzanoWeierstrassSelectorFields
                                  (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                                [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute dyadicRoute regularRoute sealRoute bUnary mUnary dUnary rUnary eUnary
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed bUnary mUnary selectedRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed selectedUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  exact
    ⟨selectedUnary, dyadicUnary, regularUnary, sealUnary, selectedRoute, dyadicRoute,
      regularRoute, sealRoute, rfl⟩

theorem BolzanoWeierstrassSelectorRegularCauchyLimitHandoff
    {B M Q W D R E H C P N dyadicRead regularRead sealRead : BHist} :
    Cont B M W →
      Cont W D dyadicRead →
        Cont dyadicRead R regularRead →
          Cont regularRead E sealRead →
            UnaryHistory B →
              UnaryHistory M →
                UnaryHistory D →
                  UnaryHistory R →
                    UnaryHistory E →
                      UnaryHistory W ∧ UnaryHistory dyadicRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ hsame H H ∧
                          Cont B M W ∧ Cont W D dyadicRead ∧
                            Cont dyadicRead R regularRead ∧ Cont regularRead E sealRead ∧
                              bolzanoWeierstrassSelectorFields
                                  (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H C P N) =
                                [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro windowRoute dyadicRoute regularRoute sealRoute bUnary mUnary dUnary rUnary eUnary
  have windowUnary : UnaryHistory W :=
    unary_cont_closed bUnary mUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  exact
    ⟨windowUnary, dyadicUnary, regularUnary, sealUnary, hsame_refl H, windowRoute,
      dyadicRoute, regularRoute, sealRoute, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
