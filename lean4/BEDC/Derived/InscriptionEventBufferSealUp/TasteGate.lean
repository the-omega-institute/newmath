import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionEventBufferSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionEventBufferSealUp : Type where
  | mk : (E W R D A H Q P N : BHist) -> InscriptionEventBufferSealUp
  deriving DecidableEq

private def inscriptionEventBufferSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionEventBufferSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionEventBufferSealEncodeBHist h

private def inscriptionEventBufferSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionEventBufferSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionEventBufferSealDecodeBHist tail)

private theorem inscriptionEventBufferSealDecodeEncodeBHist :
    ∀ h : BHist,
      inscriptionEventBufferSealDecodeBHist
        (inscriptionEventBufferSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def inscriptionEventBufferSealFields :
    InscriptionEventBufferSealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionEventBufferSealUp.mk E W R D A H Q P N => [E, W, R, D, A, H, Q, P, N]

private def inscriptionEventBufferSealToEventFlow :
    InscriptionEventBufferSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (inscriptionEventBufferSealFields x).map inscriptionEventBufferSealEncodeBHist

private def inscriptionEventBufferSealFromEventFlow :
    EventFlow -> Option InscriptionEventBufferSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | A :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (InscriptionEventBufferSealUp.mk
                                              (inscriptionEventBufferSealDecodeBHist E)
                                              (inscriptionEventBufferSealDecodeBHist W)
                                              (inscriptionEventBufferSealDecodeBHist R)
                                              (inscriptionEventBufferSealDecodeBHist D)
                                              (inscriptionEventBufferSealDecodeBHist A)
                                              (inscriptionEventBufferSealDecodeBHist H)
                                              (inscriptionEventBufferSealDecodeBHist Q)
                                              (inscriptionEventBufferSealDecodeBHist P)
                                              (inscriptionEventBufferSealDecodeBHist N))
                                      | _ :: _ => none

private theorem inscriptionEventBufferSeal_round_trip :
    ∀ x : InscriptionEventBufferSealUp,
      inscriptionEventBufferSealFromEventFlow
        (inscriptionEventBufferSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W R D A H Q P N =>
      change
        some
          (InscriptionEventBufferSealUp.mk
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist E))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist W))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist R))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist D))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist A))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist H))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist Q))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist P))
            (inscriptionEventBufferSealDecodeBHist
              (inscriptionEventBufferSealEncodeBHist N))) =
          some (InscriptionEventBufferSealUp.mk E W R D A H Q P N)
      rw [inscriptionEventBufferSealDecodeEncodeBHist E,
        inscriptionEventBufferSealDecodeEncodeBHist W,
        inscriptionEventBufferSealDecodeEncodeBHist R,
        inscriptionEventBufferSealDecodeEncodeBHist D,
        inscriptionEventBufferSealDecodeEncodeBHist A,
        inscriptionEventBufferSealDecodeEncodeBHist H,
        inscriptionEventBufferSealDecodeEncodeBHist Q,
        inscriptionEventBufferSealDecodeEncodeBHist P,
        inscriptionEventBufferSealDecodeEncodeBHist N]

private theorem inscriptionEventBufferSealToEventFlow_injective
    {x y : InscriptionEventBufferSealUp} :
    inscriptionEventBufferSealToEventFlow x =
      inscriptionEventBufferSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionEventBufferSealFromEventFlow (inscriptionEventBufferSealToEventFlow x) =
        inscriptionEventBufferSealFromEventFlow (inscriptionEventBufferSealToEventFlow y) :=
    congrArg inscriptionEventBufferSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionEventBufferSeal_round_trip x).symm
      (Eq.trans hread (inscriptionEventBufferSeal_round_trip y)))

private theorem inscriptionEventBufferSeal_fields_faithful :
    ∀ x y : InscriptionEventBufferSealUp,
      inscriptionEventBufferSealFields x = inscriptionEventBufferSealFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ W₁ R₁ D₁ A₁ H₁ Q₁ P₁ N₁ =>
      cases y with
      | mk E₂ W₂ R₂ D₂ A₂ H₂ Q₂ P₂ N₂ =>
          injection hfields with hE tail0
          injection tail0 with hW tail1
          injection tail1 with hR tail2
          injection tail2 with hD tail3
          injection tail3 with hA tail4
          injection tail4 with hH tail5
          injection tail5 with hQ tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hE
          subst hW
          subst hR
          subst hD
          subst hA
          subst hH
          subst hQ
          subst hP
          subst hN
          rfl

instance inscriptionEventBufferSealBHistCarrier :
    BHistCarrier InscriptionEventBufferSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionEventBufferSealToEventFlow
  fromEventFlow := inscriptionEventBufferSealFromEventFlow

instance inscriptionEventBufferSealChapterTasteGate :
    ChapterTasteGate InscriptionEventBufferSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionEventBufferSealFromEventFlow
        (inscriptionEventBufferSealToEventFlow x) = some x
    exact inscriptionEventBufferSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionEventBufferSealToEventFlow_injective heq)

instance inscriptionEventBufferSealFieldFaithful :
    FieldFaithful InscriptionEventBufferSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionEventBufferSealFields
  field_faithful := inscriptionEventBufferSeal_fields_faithful

instance inscriptionEventBufferSealNontrivial :
    Nontrivial InscriptionEventBufferSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscriptionEventBufferSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionEventBufferSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionEventBufferSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inscriptionEventBufferSealChapterTasteGate

theorem InscriptionEventBufferSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionEventBufferSealDecodeBHist
        (inscriptionEventBufferSealEncodeBHist h) = h) ∧
      (∀ x : InscriptionEventBufferSealUp,
        inscriptionEventBufferSealFromEventFlow
          (inscriptionEventBufferSealToEventFlow x) = some x) ∧
        (∀ x y : InscriptionEventBufferSealUp,
          inscriptionEventBufferSealToEventFlow x =
            inscriptionEventBufferSealToEventFlow y -> x = y) ∧
          inscriptionEventBufferSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionEventBufferSealDecodeEncodeBHist
  · constructor
    · exact inscriptionEventBufferSeal_round_trip
    · constructor
      · intro x y heq
        exact inscriptionEventBufferSealToEventFlow_injective heq
      · rfl

theorem InscriptionEventBufferSealCarrier_namecert_obligations {E W R D A H Q P N : BHist} :
    inscriptionEventBufferSealFields (InscriptionEventBufferSealUp.mk E W R D A H Q P N) =
        [E, W, R, D, A, H, Q, P, N] ∧
      Cont E W (append E W) ∧
        Cont R D (append R D) ∧
          Cont (append E W) (append R D) (append (append E W) (append R D)) ∧
            hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont
  constructor
  · rfl
  constructor
  · exact cont_intro rfl
  constructor
  · exact cont_intro rfl
  constructor
  · exact cont_intro rfl
  · exact hsame_refl N

def InscriptionEventBufferSealCarrier [AskSetup] [PackageSetup]
    (event window replay digest audit transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory event ∧ UnaryHistory window ∧ UnaryHistory replay ∧
    UnaryHistory digest ∧ UnaryHistory audit ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont event window replay ∧ Cont replay digest audit ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem InscriptionEventBufferSealCarrier_nonescape [AskSetup] [PackageSetup]
    {event window replay digest audit transport route provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InscriptionEventBufferSealCarrier event window replay digest audit transport route
        provenance name bundle pkg ->
      Cont audit route consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory event ∧ UnaryHistory window ∧ UnaryHistory replay ∧
            UnaryHistory digest ∧ UnaryHistory audit ∧ UnaryHistory consumer ∧
              Cont event window replay ∧ Cont replay digest audit ∧
                Cont audit route consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨eventUnary, windowUnary, replayUnary, digestUnary, auditUnary,
    _transportUnary, routeUnary, _provenanceUnary, _nameUnary, eventRoute,
    digestRoute, provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed auditUnary routeUnary consumerRoute
  exact
    ⟨eventUnary, windowUnary, replayUnary, digestUnary, auditUnary, consumerUnary,
      eventRoute, digestRoute, consumerRoute, provenancePkg, consumerPkg⟩

end BEDC.Derived.InscriptionEventBufferSealUp
