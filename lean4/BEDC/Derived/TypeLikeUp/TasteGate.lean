import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeLikeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeLikeUp : Type where
  | mk (B F Q E H C P N : BHist) : TypeLikeUp
  deriving DecidableEq

def typeLikeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeLikeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeLikeEncodeBHist h

def typeLikeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeLikeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeLikeDecodeBHist tail)

private theorem TypeLikeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, typeLikeDecodeBHist (typeLikeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typeLikeFields : TypeLikeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypeLikeUp.mk B F Q E H C P N => [B, F, Q, E, H, C, P, N]

def typeLikeToEventFlow : TypeLikeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (typeLikeFields x).map typeLikeEncodeBHist

private def typeLikeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => typeLikeEventAtDefault index rest

def typeLikeFromEventFlow : EventFlow → Option TypeLikeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TypeLikeUp.mk
        (typeLikeDecodeBHist (typeLikeEventAtDefault 0 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 1 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 2 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 3 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 4 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 5 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 6 ef))
        (typeLikeDecodeBHist (typeLikeEventAtDefault 7 ef)))

private theorem TypeLikeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TypeLikeUp, typeLikeFromEventFlow (typeLikeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F Q E H C P N =>
      change
        some
          (TypeLikeUp.mk
            (typeLikeDecodeBHist (typeLikeEncodeBHist B))
            (typeLikeDecodeBHist (typeLikeEncodeBHist F))
            (typeLikeDecodeBHist (typeLikeEncodeBHist Q))
            (typeLikeDecodeBHist (typeLikeEncodeBHist E))
            (typeLikeDecodeBHist (typeLikeEncodeBHist H))
            (typeLikeDecodeBHist (typeLikeEncodeBHist C))
            (typeLikeDecodeBHist (typeLikeEncodeBHist P))
            (typeLikeDecodeBHist (typeLikeEncodeBHist N))) =
          some (TypeLikeUp.mk B F Q E H C P N)
      rw [TypeLikeTasteGate_single_carrier_alignment_decode B,
        TypeLikeTasteGate_single_carrier_alignment_decode F,
        TypeLikeTasteGate_single_carrier_alignment_decode Q,
        TypeLikeTasteGate_single_carrier_alignment_decode E,
        TypeLikeTasteGate_single_carrier_alignment_decode H,
        TypeLikeTasteGate_single_carrier_alignment_decode C,
        TypeLikeTasteGate_single_carrier_alignment_decode P,
        TypeLikeTasteGate_single_carrier_alignment_decode N]

private theorem typeLikeToEventFlow_injective {x y : TypeLikeUp} :
    typeLikeToEventFlow x = typeLikeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeLikeFromEventFlow (typeLikeToEventFlow x) =
        typeLikeFromEventFlow (typeLikeToEventFlow y) :=
    congrArg typeLikeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TypeLikeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TypeLikeTasteGate_single_carrier_alignment_round_trip y)))

instance typeLikeBHistCarrier : BHistCarrier TypeLikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeLikeToEventFlow
  fromEventFlow := typeLikeFromEventFlow

instance typeLikeChapterTasteGate : ChapterTasteGate TypeLikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typeLikeFromEventFlow (typeLikeToEventFlow x) = some x
    exact TypeLikeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typeLikeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TypeLikeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typeLikeChapterTasteGate

theorem TypeLikeTasteGate_single_carrier_alignment :
    (∀ h : BHist, typeLikeDecodeBHist (typeLikeEncodeBHist h) = h) ∧
      (∀ x : TypeLikeUp, typeLikeFromEventFlow (typeLikeToEventFlow x) = some x) ∧
        (∀ x y : TypeLikeUp, typeLikeToEventFlow x = typeLikeToEventFlow y -> x = y) ∧
          typeLikeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact TypeLikeTasteGate_single_carrier_alignment_decode
  constructor
  · exact TypeLikeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact typeLikeToEventFlow_injective heq
  · rfl

theorem TypeLikeNameCertObligations
    {B F Q E H C P N fiber classifier endpoint transport replay provenance nameRoute : BHist} :
    UnaryHistory B ->
      UnaryHistory F ->
        UnaryHistory Q ->
          UnaryHistory E ->
            UnaryHistory H ->
              UnaryHistory C ->
                UnaryHistory P ->
                  UnaryHistory N ->
                    Cont B F fiber ->
                      Cont fiber Q classifier ->
                        Cont classifier E endpoint ->
                          Cont endpoint H transport ->
                            Cont transport C replay ->
                              Cont replay P provenance ->
                                Cont provenance N nameRoute ->
                                  UnaryHistory fiber ∧
                                    UnaryHistory classifier ∧
                                      UnaryHistory endpoint ∧
                                        UnaryHistory transport ∧
                                          UnaryHistory replay ∧
                                            UnaryHistory provenance ∧
                                              UnaryHistory nameRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro baseUnary fiberUnary classifierUnary endpointUnary transportUnary replayUnary
    provenanceUnary nameUnary fiberCont classifierCont endpointCont transportCont replayCont
    provenanceCont nameCont
  have fiberClosed : UnaryHistory fiber :=
    unary_cont_closed baseUnary fiberUnary fiberCont
  have classifierClosed : UnaryHistory classifier :=
    unary_cont_closed fiberClosed classifierUnary classifierCont
  have endpointClosed : UnaryHistory endpoint :=
    unary_cont_closed classifierClosed endpointUnary endpointCont
  have transportClosed : UnaryHistory transport :=
    unary_cont_closed endpointClosed transportUnary transportCont
  have replayClosed : UnaryHistory replay :=
    unary_cont_closed transportClosed replayUnary replayCont
  have provenanceClosed : UnaryHistory provenance :=
    unary_cont_closed replayClosed provenanceUnary provenanceCont
  have nameClosed : UnaryHistory nameRoute :=
    unary_cont_closed provenanceClosed nameUnary nameCont
  exact
    ⟨fiberClosed, classifierClosed, endpointClosed, transportClosed, replayClosed,
      provenanceClosed, nameClosed⟩

end BEDC.Derived.TypeLikeUp
