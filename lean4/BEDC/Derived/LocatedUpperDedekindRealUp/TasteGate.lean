import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUpperDedekindRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUpperDedekindRealUp : Type where
  | mk (D A L O E H C P N : BHist) : LocatedUpperDedekindRealUp
  deriving DecidableEq

def locatedUpperDedekindRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUpperDedekindRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUpperDedekindRealEncodeBHist h

def locatedUpperDedekindRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUpperDedekindRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUpperDedekindRealDecodeBHist tail)

private theorem LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUpperDedekindRealToEventFlow : LocatedUpperDedekindRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUpperDedekindRealUp.mk D A L O E H C P N =>
      [[BMark.b0],
        locatedUpperDedekindRealEncodeBHist D,
        [BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedUpperDedekindRealEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedUpperDedekindRealEncodeBHist N]

def locatedUpperDedekindRealFromEventFlow : EventFlow -> Option LocatedUpperDedekindRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagD :: restD =>
      match restD with
      | [] => none
      | D :: restATag =>
          match restATag with
          | [] => none
          | _tagA :: restA =>
              match restA with
              | [] => none
              | A :: restLTag =>
                  match restLTag with
                  | [] => none
                  | _tagL :: restL =>
                      match restL with
                      | [] => none
                      | L :: restOTag =>
                          match restOTag with
                          | [] => none
                          | _tagO :: restO =>
                              match restO with
                              | [] => none
                              | O :: restETag =>
                                  match restETag with
                                  | [] => none
                                  | _tagE :: restE =>
                                      match restE with
                                      | [] => none
                                      | E :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restCTag =>
                                                  match restCTag with
                                                  | [] => none
                                                  | _tagC :: restC =>
                                                      match restC with
                                                      | [] => none
                                                      | C :: restPTag =>
                                                          match restPTag with
                                                          | [] => none
                                                          | _tagP :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (LocatedUpperDedekindRealUp.mk
                                                                                  (locatedUpperDedekindRealDecodeBHist D)
                                                                                  (locatedUpperDedekindRealDecodeBHist A)
                                                                                  (locatedUpperDedekindRealDecodeBHist L)
                                                                                  (locatedUpperDedekindRealDecodeBHist O)
                                                                                  (locatedUpperDedekindRealDecodeBHist E)
                                                                                  (locatedUpperDedekindRealDecodeBHist H)
                                                                                  (locatedUpperDedekindRealDecodeBHist C)
                                                                                  (locatedUpperDedekindRealDecodeBHist P)
                                                                                  (locatedUpperDedekindRealDecodeBHist N))
                                                                          | _ :: _ => none

private theorem LocatedUpperDedekindRealTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedUpperDedekindRealUp,
      locatedUpperDedekindRealFromEventFlow (locatedUpperDedekindRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D A L O E H C P N =>
      change
        some
          (LocatedUpperDedekindRealUp.mk
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist D))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist A))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist L))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist O))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist E))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist H))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist C))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist P))
            (locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist N))) =
          some (LocatedUpperDedekindRealUp.mk D A L O E H C P N)
      rw [LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode D,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode A,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode L,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode O,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode E,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode H,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode C,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode P,
        LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode N]

private theorem LocatedUpperDedekindRealTasteGate_single_carrier_alignment_injective
    {x y : LocatedUpperDedekindRealUp} :
    locatedUpperDedekindRealToEventFlow x = locatedUpperDedekindRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUpperDedekindRealFromEventFlow (locatedUpperDedekindRealToEventFlow x) =
        locatedUpperDedekindRealFromEventFlow (locatedUpperDedekindRealToEventFlow y) :=
    congrArg locatedUpperDedekindRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedUpperDedekindRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedUpperDedekindRealTasteGate_single_carrier_alignment_round_trip y)))

private def locatedUpperDedekindRealFields : LocatedUpperDedekindRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUpperDedekindRealUp.mk D A L O E H C P N => [D, A, L, O, E, H, C, P, N]

private theorem LocatedUpperDedekindRealTasteGate_single_carrier_alignment_fields :
    forall x y : LocatedUpperDedekindRealUp,
      locatedUpperDedekindRealFields x = locatedUpperDedekindRealFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 A1 L1 O1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 A2 L2 O2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedUpperDedekindRealBHistCarrier : BHistCarrier LocatedUpperDedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUpperDedekindRealToEventFlow
  fromEventFlow := locatedUpperDedekindRealFromEventFlow

instance locatedUpperDedekindRealChapterTasteGate :
    ChapterTasteGate LocatedUpperDedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUpperDedekindRealFromEventFlow (locatedUpperDedekindRealToEventFlow x) = some x
    exact LocatedUpperDedekindRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedUpperDedekindRealTasteGate_single_carrier_alignment_injective heq)

instance locatedUpperDedekindRealFieldFaithful : FieldFaithful LocatedUpperDedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedUpperDedekindRealFields
  field_faithful := LocatedUpperDedekindRealTasteGate_single_carrier_alignment_fields

instance locatedUpperDedekindRealNontrivial : Nontrivial LocatedUpperDedekindRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedUpperDedekindRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedUpperDedekindRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedUpperDedekindRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedUpperDedekindRealUp) ∧
      Nonempty (FieldFaithful LocatedUpperDedekindRealUp) ∧
      Nonempty (Nontrivial LocatedUpperDedekindRealUp) ∧
      (∀ h : BHist,
        locatedUpperDedekindRealDecodeBHist (locatedUpperDedekindRealEncodeBHist h) = h) ∧
      (∀ x : LocatedUpperDedekindRealUp,
        locatedUpperDedekindRealFromEventFlow (locatedUpperDedekindRealToEventFlow x) =
          some x) ∧
      (∀ x y : LocatedUpperDedekindRealUp,
        locatedUpperDedekindRealToEventFlow x = locatedUpperDedekindRealToEventFlow y → x = y) ∧
      locatedUpperDedekindRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨locatedUpperDedekindRealChapterTasteGate⟩
  constructor
  · exact ⟨locatedUpperDedekindRealFieldFaithful⟩
  constructor
  · exact ⟨locatedUpperDedekindRealNontrivial⟩
  constructor
  · exact LocatedUpperDedekindRealTasteGate_single_carrier_alignment_decode
  constructor
  · exact LocatedUpperDedekindRealTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact LocatedUpperDedekindRealTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.LocatedUpperDedekindRealUp.TasteGate
