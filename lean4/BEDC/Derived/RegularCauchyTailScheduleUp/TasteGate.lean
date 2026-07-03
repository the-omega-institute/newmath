import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailScheduleUp : Type where
  | mk (Q R W D K T M F E H C P N : BHist) : RegularCauchyTailScheduleUp
  deriving DecidableEq

def RegularCauchyTailScheduleCarrier [AskSetup] [PackageSetup]
    (precision source window dyadic cofinal tail meet fusion sealRow transport route provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory source ∧
      UnaryHistory window ∧
        UnaryHistory dyadic ∧
          UnaryHistory cofinal ∧
            UnaryHistory tail ∧
              UnaryHistory meet ∧
                UnaryHistory fusion ∧
                  UnaryHistory sealRow ∧
                    UnaryHistory transport ∧
                      UnaryHistory route ∧
                        UnaryHistory provenance ∧
                          UnaryHistory name ∧
                            Cont precision source route ∧
                              Cont route window tail ∧
                                Cont tail meet fusion ∧
                                  Cont fusion sealRow transport ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle name pkg

def regularCauchyTailScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailScheduleEncodeBHist h

def regularCauchyTailScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailScheduleDecodeBHist tail)

private theorem regularCauchyTailScheduleDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailScheduleDecodeBHist
        (regularCauchyTailScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailScheduleFields :
    RegularCauchyTailScheduleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N =>
      [Q, R, W, D, K, T, M, F, E, H, C, P, N]

def regularCauchyTailScheduleToEventFlow :
    RegularCauchyTailScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailScheduleFields x).map regularCauchyTailScheduleEncodeBHist

def regularCauchyTailScheduleFromEventFlow :
    EventFlow → Option RegularCauchyTailScheduleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | K :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | M :: rest6 =>
                              match rest6 with
                              | [] => none
                              | F :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (RegularCauchyTailScheduleUp.mk
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                Q)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                R)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                W)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                D)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                K)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                T)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                M)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                F)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                E)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                H)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                C)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                P)
                                                              (regularCauchyTailScheduleDecodeBHist
                                                                N))
                                                      | _ :: _ => none

private theorem regularCauchyTailSchedule_mk_congr
    {Q Q' R R' W W' D D' K K' T T' M M' F F' E E' H H' C C' P P' N N' :
      BHist}
    (hQ : Q' = Q)
    (hR : R' = R)
    (hW : W' = W)
    (hD : D' = D)
    (hK : K' = K)
    (hT : T' = T)
    (hM : M' = M)
    (hF : F' = F)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RegularCauchyTailScheduleUp.mk Q' R' W' D' K' T' M' F' E' H' C' P' N' =
      RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hR
  cases hW
  cases hD
  cases hK
  cases hT
  cases hM
  cases hF
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem regularCauchyTailSchedule_round_trip :
    ∀ x : RegularCauchyTailScheduleUp,
      regularCauchyTailScheduleFromEventFlow
        (regularCauchyTailScheduleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q R W D K T M F E H C P N =>
      change
        some
          (RegularCauchyTailScheduleUp.mk
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist Q))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist R))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist W))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist D))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist K))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist T))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist M))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist F))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist E))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist H))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist C))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist P))
            (regularCauchyTailScheduleDecodeBHist
              (regularCauchyTailScheduleEncodeBHist N))) =
          some (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)
      exact
        congrArg some
          (regularCauchyTailSchedule_mk_congr
            (regularCauchyTailScheduleDecode_encode_bhist Q)
            (regularCauchyTailScheduleDecode_encode_bhist R)
            (regularCauchyTailScheduleDecode_encode_bhist W)
            (regularCauchyTailScheduleDecode_encode_bhist D)
            (regularCauchyTailScheduleDecode_encode_bhist K)
            (regularCauchyTailScheduleDecode_encode_bhist T)
            (regularCauchyTailScheduleDecode_encode_bhist M)
            (regularCauchyTailScheduleDecode_encode_bhist F)
            (regularCauchyTailScheduleDecode_encode_bhist E)
            (regularCauchyTailScheduleDecode_encode_bhist H)
            (regularCauchyTailScheduleDecode_encode_bhist C)
            (regularCauchyTailScheduleDecode_encode_bhist P)
            (regularCauchyTailScheduleDecode_encode_bhist N))

private theorem regularCauchyTailScheduleToEventFlow_injective
    {x y : RegularCauchyTailScheduleUp} :
    regularCauchyTailScheduleToEventFlow x =
      regularCauchyTailScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk Q R W D K T M F E H C P N =>
      cases y with
      | mk Q' R' W' D' K' T' M' F' E' H' C' P' N' =>
          change
            [regularCauchyTailScheduleEncodeBHist Q,
              regularCauchyTailScheduleEncodeBHist R,
              regularCauchyTailScheduleEncodeBHist W,
              regularCauchyTailScheduleEncodeBHist D,
              regularCauchyTailScheduleEncodeBHist K,
              regularCauchyTailScheduleEncodeBHist T,
              regularCauchyTailScheduleEncodeBHist M,
              regularCauchyTailScheduleEncodeBHist F,
              regularCauchyTailScheduleEncodeBHist E,
              regularCauchyTailScheduleEncodeBHist H,
              regularCauchyTailScheduleEncodeBHist C,
              regularCauchyTailScheduleEncodeBHist P,
              regularCauchyTailScheduleEncodeBHist N] =
                [regularCauchyTailScheduleEncodeBHist Q',
                  regularCauchyTailScheduleEncodeBHist R',
                  regularCauchyTailScheduleEncodeBHist W',
                  regularCauchyTailScheduleEncodeBHist D',
                  regularCauchyTailScheduleEncodeBHist K',
                  regularCauchyTailScheduleEncodeBHist T',
                  regularCauchyTailScheduleEncodeBHist M',
                  regularCauchyTailScheduleEncodeBHist F',
                  regularCauchyTailScheduleEncodeBHist E',
                  regularCauchyTailScheduleEncodeBHist H',
                  regularCauchyTailScheduleEncodeBHist C',
                  regularCauchyTailScheduleEncodeBHist P',
                  regularCauchyTailScheduleEncodeBHist N'] at heq
          injection heq with hQ htail0
          injection htail0 with hR htail1
          injection htail1 with hW htail2
          injection htail2 with hD htail3
          injection htail3 with hK htail4
          injection htail4 with hT htail5
          injection htail5 with hM htail6
          injection htail6 with hF htail7
          injection htail7 with hE htail8
          injection htail8 with hH htail9
          injection htail9 with hC htail10
          injection htail10 with hP htail11
          injection htail11 with hN _hNil
          have qEq : Q = Q' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hQ
            rw [regularCauchyTailScheduleDecode_encode_bhist Q,
              regularCauchyTailScheduleDecode_encode_bhist Q'] at decoded
            exact decoded
          have rEq : R = R' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hR
            rw [regularCauchyTailScheduleDecode_encode_bhist R,
              regularCauchyTailScheduleDecode_encode_bhist R'] at decoded
            exact decoded
          have wEq : W = W' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hW
            rw [regularCauchyTailScheduleDecode_encode_bhist W,
              regularCauchyTailScheduleDecode_encode_bhist W'] at decoded
            exact decoded
          have dEq : D = D' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hD
            rw [regularCauchyTailScheduleDecode_encode_bhist D,
              regularCauchyTailScheduleDecode_encode_bhist D'] at decoded
            exact decoded
          have kEq : K = K' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hK
            rw [regularCauchyTailScheduleDecode_encode_bhist K,
              regularCauchyTailScheduleDecode_encode_bhist K'] at decoded
            exact decoded
          have tEq : T = T' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hT
            rw [regularCauchyTailScheduleDecode_encode_bhist T,
              regularCauchyTailScheduleDecode_encode_bhist T'] at decoded
            exact decoded
          have mEq : M = M' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hM
            rw [regularCauchyTailScheduleDecode_encode_bhist M,
              regularCauchyTailScheduleDecode_encode_bhist M'] at decoded
            exact decoded
          have fEq : F = F' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hF
            rw [regularCauchyTailScheduleDecode_encode_bhist F,
              regularCauchyTailScheduleDecode_encode_bhist F'] at decoded
            exact decoded
          have eEq : E = E' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hE
            rw [regularCauchyTailScheduleDecode_encode_bhist E,
              regularCauchyTailScheduleDecode_encode_bhist E'] at decoded
            exact decoded
          have hEq : H = H' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hH
            rw [regularCauchyTailScheduleDecode_encode_bhist H,
              regularCauchyTailScheduleDecode_encode_bhist H'] at decoded
            exact decoded
          have cEq : C = C' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hC
            rw [regularCauchyTailScheduleDecode_encode_bhist C,
              regularCauchyTailScheduleDecode_encode_bhist C'] at decoded
            exact decoded
          have pEq : P = P' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hP
            rw [regularCauchyTailScheduleDecode_encode_bhist P,
              regularCauchyTailScheduleDecode_encode_bhist P'] at decoded
            exact decoded
          have nEq : N = N' := by
            have decoded := congrArg regularCauchyTailScheduleDecodeBHist hN
            rw [regularCauchyTailScheduleDecode_encode_bhist N,
              regularCauchyTailScheduleDecode_encode_bhist N'] at decoded
            exact decoded
          cases qEq
          cases rEq
          cases wEq
          cases dEq
          cases kEq
          cases tEq
          cases mEq
          cases fEq
          cases eEq
          cases hEq
          cases cEq
          cases pEq
          cases nEq
          rfl

private theorem regularCauchyTailSchedule_fields_faithful :
    ∀ x y : RegularCauchyTailScheduleUp,
      regularCauchyTailScheduleFields x =
        regularCauchyTailScheduleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q R W D K T M F E H C P N =>
      cases y with
      | mk Q' R' W' D' K' T' M' F' E' H' C' P' N' =>
          injection hfields with hQ htail0
          injection htail0 with hR htail1
          injection htail1 with hW htail2
          injection htail2 with hD htail3
          injection htail3 with hK htail4
          injection htail4 with hT htail5
          injection htail5 with hM htail6
          injection htail6 with hF htail7
          injection htail7 with hE htail8
          injection htail8 with hH htail9
          injection htail9 with hC htail10
          injection htail10 with hP htail11
          injection htail11 with hN _hNil
          cases hQ
          cases hR
          cases hW
          cases hD
          cases hK
          cases hT
          cases hM
          cases hF
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance regularCauchyTailScheduleBHistCarrier :
    BHistCarrier RegularCauchyTailScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailScheduleToEventFlow
  fromEventFlow := regularCauchyTailScheduleFromEventFlow

instance regularCauchyTailScheduleChapterTasteGate :
    ChapterTasteGate RegularCauchyTailScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := regularCauchyTailSchedule_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailScheduleToEventFlow_injective heq)

instance regularCauchyTailScheduleFieldFaithful :
    FieldFaithful RegularCauchyTailScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailScheduleFields
  field_faithful := regularCauchyTailSchedule_fields_faithful

def taste_gate : ChapterTasteGate RegularCauchyTailScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailScheduleChapterTasteGate

theorem RegularCauchyTailScheduleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailScheduleDecodeBHist
        (regularCauchyTailScheduleEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailScheduleUp,
        regularCauchyTailScheduleFromEventFlow
          (regularCauchyTailScheduleToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailScheduleUp,
          regularCauchyTailScheduleToEventFlow x =
            regularCauchyTailScheduleToEventFlow y → x = y) ∧
          regularCauchyTailScheduleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTailScheduleDecode_encode_bhist
  · constructor
    · exact regularCauchyTailSchedule_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailScheduleToEventFlow_injective heq
      · rfl

theorem RegularCauchyTailSchedule_seal_facing_route_determinacy
    {Q R W D K T M F E E' H C P N route tailRead meetRead fusionRead sealRead sealRead' :
      BHist} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory M ->
            UnaryHistory F ->
              Cont Q R route ->
                Cont route W tailRead ->
                  Cont tailRead M meetRead ->
                    Cont meetRead F fusionRead ->
                      Cont fusionRead E sealRead ->
                        Cont fusionRead E' sealRead' ->
                          hsame E E' ->
                            hsame sealRead sealRead' ∧
                              regularCauchyTailScheduleFromEventFlow
                                  (regularCauchyTailScheduleToEventFlow
                                    (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)) =
                                some
                                  (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory hsame
  intro unaryQ unaryR unaryW unaryM unaryF routeQR routeTail routeMeet routeFusion sealRoute
    sealRoute' sameEndpoint
  have unaryRoute : UnaryHistory route := unary_cont_closed unaryQ unaryR routeQR
  have unaryTailRead : UnaryHistory tailRead :=
    unary_cont_closed unaryRoute unaryW routeTail
  have unaryMeetRead : UnaryHistory meetRead :=
    unary_cont_closed unaryTailRead unaryM routeMeet
  have unaryFusionRead : UnaryHistory fusionRead :=
    unary_cont_closed unaryMeetRead unaryF routeFusion
  constructor
  · exact
      cont_respects_hsame (hsame_refl fusionRead) sameEndpoint sealRoute sealRoute'
  · exact
      regularCauchyTailSchedule_round_trip
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)

theorem RegularCauchyTailSchedule_scope_binding
    {Q R W D K T M F E H C P N route tailRead meetRead fusionRead sealRead : BHist} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory M ->
            UnaryHistory F ->
              Cont Q R route ->
                Cont route W tailRead ->
                  Cont tailRead M meetRead ->
                    Cont meetRead F fusionRead ->
                      Cont fusionRead E sealRead ->
                        UnaryHistory route ∧
                          UnaryHistory tailRead ∧
                            UnaryHistory meetRead ∧
                              UnaryHistory fusionRead ∧
                                hsame sealRead (append fusionRead E) ∧
                                  regularCauchyTailScheduleFromEventFlow
                                      (regularCauchyTailScheduleToEventFlow
                                        (RegularCauchyTailScheduleUp.mk
                                          Q R W D K T M F E H C P N)) =
                                    some
                                      (RegularCauchyTailScheduleUp.mk
                                        Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory hsame
  intro unaryQ unaryR unaryW unaryM unaryF routeQR routeTail routeMeet routeFusion sealRoute
  have unaryRoute : UnaryHistory route := unary_cont_closed unaryQ unaryR routeQR
  have unaryTailRead : UnaryHistory tailRead :=
    unary_cont_closed unaryRoute unaryW routeTail
  have unaryMeetRead : UnaryHistory meetRead :=
    unary_cont_closed unaryTailRead unaryM routeMeet
  have unaryFusionRead : UnaryHistory fusionRead :=
    unary_cont_closed unaryMeetRead unaryF routeFusion
  exact
    ⟨unaryRoute, unaryTailRead, unaryMeetRead, unaryFusionRead, sealRoute,
      regularCauchyTailSchedule_round_trip
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)⟩

theorem RegularCauchyTailScheduleObligationTriad [AskSetup] [PackageSetup]
    {precision source window dyadic cofinal tail meet fusion sealRow transport route provenance
      name scheduleRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier precision source window dyadic cofinal tail meet
        fusion sealRow transport route provenance name bundle pkg →
      Cont precision window scheduleRead →
        Cont scheduleRead tail handoffRead →
          PkgSig bundle handoffRead pkg →
            UnaryHistory precision ∧
              UnaryHistory window ∧
                UnaryHistory scheduleRead ∧
                  UnaryHistory tail ∧
                    UnaryHistory handoffRead ∧
                      Cont precision window scheduleRead ∧
                        Cont scheduleRead tail handoffRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier scheduleRoute handoffRoute handoffPkg
  rcases carrier with
    ⟨precisionUnary, _sourceUnary, windowUnary, _dyadicUnary, _cofinalUnary,
      tailUnary, _meetUnary, _fusionUnary, _sealUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameUnary, _precisionRoute, _tailRoute, _fusionRoute,
      _sealRoute, provenancePkg, _namePkg⟩
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed precisionUnary windowUnary scheduleRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed scheduleReadUnary tailUnary handoffRoute
  exact
    ⟨precisionUnary, windowUnary, scheduleReadUnary, tailUnary, handoffReadUnary,
      scheduleRoute, handoffRoute, provenancePkg, handoffPkg⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
