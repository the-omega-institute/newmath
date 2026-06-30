import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCutCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCutCompletionUp : Type where
  | mk (Bm Bp G W R D E H C P N : BHist) : LocatedCutCompletionUp
  deriving DecidableEq

def locatedCutCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCutCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCutCompletionEncodeBHist h

def locatedCutCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCutCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCutCompletionDecodeBHist tail)

private theorem locatedCutCompletionDecode_encode_bhist :
    ∀ h : BHist,
      locatedCutCompletionDecodeBHist (locatedCutCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCutCompletionFields : LocatedCutCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCutCompletionUp.mk Bm Bp G W R D E H C P N =>
      [Bm, Bp, G, W, R, D, E, H, C, P, N]

def locatedCutCompletionToEventFlow : LocatedCutCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCutCompletionFields x).map locatedCutCompletionEncodeBHist

def locatedCutCompletionFromEventFlow : EventFlow → Option LocatedCutCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | Bm :: Bp :: G :: W :: R :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (LocatedCutCompletionUp.mk
          (locatedCutCompletionDecodeBHist Bm)
          (locatedCutCompletionDecodeBHist Bp)
          (locatedCutCompletionDecodeBHist G)
          (locatedCutCompletionDecodeBHist W)
          (locatedCutCompletionDecodeBHist R)
          (locatedCutCompletionDecodeBHist D)
          (locatedCutCompletionDecodeBHist E)
          (locatedCutCompletionDecodeBHist H)
          (locatedCutCompletionDecodeBHist C)
          (locatedCutCompletionDecodeBHist P)
          (locatedCutCompletionDecodeBHist N))
  | _ => none

private theorem locatedCutCompletion_round_trip :
    ∀ x : LocatedCutCompletionUp,
      locatedCutCompletionFromEventFlow (locatedCutCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Bm Bp G W R D E H C P N =>
      simp only [locatedCutCompletionToEventFlow, locatedCutCompletionFields,
        locatedCutCompletionFromEventFlow, locatedCutCompletionDecode_encode_bhist,
        List.map_cons, List.map_nil]

private theorem locatedCutCompletionToEventFlow_injective
    {x y : LocatedCutCompletionUp} :
    locatedCutCompletionToEventFlow x = locatedCutCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x =
          locatedCutCompletionFromEventFlow (locatedCutCompletionToEventFlow x) :=
        (locatedCutCompletion_round_trip x).symm
      _ =
          locatedCutCompletionFromEventFlow (locatedCutCompletionToEventFlow y) :=
        congrArg locatedCutCompletionFromEventFlow heq
      _ = some y := locatedCutCompletion_round_trip y
  exact Option.some.inj optionEq

private theorem locatedCutCompletion_fields_faithful :
    ∀ x y : LocatedCutCompletionUp,
      locatedCutCompletionFields x = locatedCutCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Bm1 Bp1 G1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Bm2 Bp2 G2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          injection h with hBm t1
          injection t1 with hBp t2
          injection t2 with hG t3
          injection t3 with hW t4
          injection t4 with hR t5
          injection t5 with hD t6
          injection t6 with hE t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          cases hBm
          cases hBp
          cases hG
          cases hW
          cases hR
          cases hD
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance locatedCutCompletionBHistCarrier : BHistCarrier LocatedCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCutCompletionToEventFlow
  fromEventFlow := locatedCutCompletionFromEventFlow

instance locatedCutCompletionChapterTasteGate : ChapterTasteGate LocatedCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCutCompletionFromEventFlow (locatedCutCompletionToEventFlow x) = some x
    exact locatedCutCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCutCompletionToEventFlow_injective heq)

instance locatedCutCompletionFieldFaithful : FieldFaithful LocatedCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCutCompletionFields
  field_faithful := locatedCutCompletion_fields_faithful

instance locatedCutCompletionNontrivial : Nontrivial LocatedCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCutCompletionUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCutCompletionUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCutCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCutCompletionChapterTasteGate

theorem LocatedCutCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        locatedCutCompletionDecodeBHist (locatedCutCompletionEncodeBHist h) = h) ∧
      (∀ x y : LocatedCutCompletionUp,
        locatedCutCompletionFields x = locatedCutCompletionFields y → x = y) ∧
      (∃ x y : LocatedCutCompletionUp, x ≠ y) ∧
      (locatedCutCompletionFields
          (LocatedCutCompletionUp.mk
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x y hfields
      cases x with
      | mk Bm1 Bp1 G1 W1 R1 D1 E1 H1 C1 P1 N1 =>
          cases y with
          | mk Bm2 Bp2 G2 W2 R2 D2 E2 H2 C2 P2 N2 =>
              cases hfields
              rfl
    · constructor
      · exact
          ⟨LocatedCutCompletionUp.mk
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            LocatedCutCompletionUp.mk
              (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩
      · rfl

end BEDC.Derived.LocatedCutCompletionUp
