import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeanoCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeanoCurveUp : Type where
  | mk (I G S X Y E R H C Q N : BHist) : PeanoCurveUp
  deriving DecidableEq

private def peanoCurveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: peanoCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: peanoCurveEncodeBHist h

private def peanoCurveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (peanoCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (peanoCurveDecodeBHist tail)

private theorem peanoCurve_decode_encode_bhist :
    ∀ h : BHist, peanoCurveDecodeBHist (peanoCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def peanoCurveFields : PeanoCurveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoCurveUp.mk I G S X Y E R H C Q N => [I, G, S, X, Y, E, R, H, C, Q, N]

private def peanoCurveToEventFlow : PeanoCurveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoCurveUp.mk I G S X Y E R H C Q N =>
      [peanoCurveEncodeBHist I,
        peanoCurveEncodeBHist G,
        peanoCurveEncodeBHist S,
        peanoCurveEncodeBHist X,
        peanoCurveEncodeBHist Y,
        peanoCurveEncodeBHist E,
        peanoCurveEncodeBHist R,
        peanoCurveEncodeBHist H,
        peanoCurveEncodeBHist C,
        peanoCurveEncodeBHist Q,
        peanoCurveEncodeBHist N]

private def peanoCurveRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => peanoCurveRawAt n rest

private def peanoCurveLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => peanoCurveLengthEq n rest

private def peanoCurveFromEventFlow : EventFlow → Option PeanoCurveUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match peanoCurveLengthEq 11 flow with
      | true =>
          some
            (PeanoCurveUp.mk
              (peanoCurveDecodeBHist (peanoCurveRawAt 0 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 1 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 2 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 3 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 4 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 5 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 6 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 7 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 8 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 9 flow))
              (peanoCurveDecodeBHist (peanoCurveRawAt 10 flow)))
      | false => none

private theorem peanoCurve_round_trip :
    ∀ x : PeanoCurveUp,
      peanoCurveFromEventFlow (peanoCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I G S X Y E R H C Q N =>
      change
        some
          (PeanoCurveUp.mk
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist I))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist G))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist S))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist X))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist Y))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist E))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist R))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist H))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist C))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist Q))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist N))) =
          some (PeanoCurveUp.mk I G S X Y E R H C Q N)
      rw [peanoCurve_decode_encode_bhist I,
        peanoCurve_decode_encode_bhist G,
        peanoCurve_decode_encode_bhist S,
        peanoCurve_decode_encode_bhist X,
        peanoCurve_decode_encode_bhist Y,
        peanoCurve_decode_encode_bhist E,
        peanoCurve_decode_encode_bhist R,
        peanoCurve_decode_encode_bhist H,
        peanoCurve_decode_encode_bhist C,
        peanoCurve_decode_encode_bhist Q,
        peanoCurve_decode_encode_bhist N]

private theorem peanoCurveToEventFlow_injective {x y : PeanoCurveUp} :
    peanoCurveToEventFlow x = peanoCurveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      peanoCurveFromEventFlow (peanoCurveToEventFlow x) =
        peanoCurveFromEventFlow (peanoCurveToEventFlow y) :=
    congrArg peanoCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (peanoCurve_round_trip x).symm
      (Eq.trans hread (peanoCurve_round_trip y)))

private theorem peanoCurve_field_faithful :
    ∀ x y : PeanoCurveUp, peanoCurveFields x = peanoCurveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 G1 S1 X1 Y1 E1 R1 H1 C1 Q1 N1 =>
      cases y with
      | mk I2 G2 S2 X2 Y2 E2 R2 H2 C2 Q2 N2 =>
          cases h
          rfl

instance peanoCurveBHistCarrier : BHistCarrier PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := peanoCurveToEventFlow
  fromEventFlow := peanoCurveFromEventFlow

instance peanoCurveChapterTasteGate : ChapterTasteGate PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change peanoCurveFromEventFlow (peanoCurveToEventFlow x) = some x
    exact peanoCurve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (peanoCurveToEventFlow_injective heq)

instance peanoCurveFieldFaithful : FieldFaithful PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := peanoCurveFields
  field_faithful := peanoCurve_field_faithful

instance peanoCurveNontrivial : Nontrivial PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PeanoCurveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PeanoCurveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PeanoCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  peanoCurveChapterTasteGate

def PeanoCurveCarrier (I G S X Y E R H C Q N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory I ∧ UnaryHistory G ∧ UnaryHistory S ∧ UnaryHistory X ∧
    UnaryHistory Y ∧ UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N

theorem PeanoCurveCarrier_namecert_obligations
    {I G S X Y E R H C Q N gridRead coordinateRead consumerRead : BHist} :
    PeanoCurveCarrier I G S X Y E R H C Q N →
      Cont I G gridRead →
        Cont gridRead X coordinateRead →
          Cont coordinateRead C consumerRead →
            SemanticNameCert
              (fun row : BHist =>
                List.Mem row (peanoCurveFields (PeanoCurveUp.mk I G S X Y E R H C Q N)))
              (fun row : BHist =>
                List.Mem row (peanoCurveFields (PeanoCurveUp.mk I G S X Y E R H C Q N)) ∨
                  hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧
                  (hsame row consumerRead ∨
                    List.Mem row
                      (peanoCurveFields (PeanoCurveUp.mk I G S X Y E R H C Q N))))
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier gridRoute coordinateRoute consumerRoute
  obtain ⟨intervalUnary, gridUnary, siblingUnary, coordinateXUnary, coordinateYUnary,
    errorUnary, surjectionUnary, transportUnary, replayUnary, provenanceUnary,
    nameUnary⟩ := carrier
  have gridReadUnary : UnaryHistory gridRead :=
    unary_cont_closed intervalUnary gridUnary gridRoute
  have coordinateReadUnary : UnaryHistory coordinateRead :=
    unary_cont_closed gridReadUnary coordinateXUnary coordinateRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed coordinateReadUnary replayUnary consumerRoute
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact ⟨I, List.Mem.head _⟩
  · intro h _source
    exact hsame_refl h
  · intro h k same
    exact hsame_symm same
  · intro h k r sameHK sameKR
    exact hsame_trans sameHK sameKR
  · intro h k same source
    cases same
    exact source
  · intro h source
    exact Or.inl source
  · intro h source
    constructor
    · change List.Mem h [I, G, S, X, Y, E, R, H, C, Q, N] at source
      cases source with
      | head =>
        exact intervalUnary
      | tail _ source =>
          cases source with
          | head =>
              exact gridUnary
          | tail _ source =>
              cases source with
              | head =>
                  exact siblingUnary
              | tail _ source =>
                  cases source with
                  | head =>
                      exact coordinateXUnary
                  | tail _ source =>
                      cases source with
                      | head =>
                          exact coordinateYUnary
                      | tail _ source =>
                          cases source with
                          | head =>
                              exact errorUnary
                          | tail _ source =>
                              cases source with
                              | head =>
                                  exact surjectionUnary
                              | tail _ source =>
                                  cases source with
                                  | head =>
                                      exact transportUnary
                                  | tail _ source =>
                                      cases source with
                                      | head =>
                                          exact replayUnary
                                      | tail _ source =>
                                          cases source with
                                          | head =>
                                              exact provenanceUnary
                                          | tail _ source =>
                                              cases source with
                                              | head =>
                                                  exact nameUnary
                                              | tail _ source =>
                                                  cases source
    · exact Or.inr source

end BEDC.Derived.PeanoCurveUp
