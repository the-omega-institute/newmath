import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletApproximationUp : Type where
  | mk (Q B M D S G R E H C P N : BHist) : DirichletApproximationUp

def dirichletApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletApproximationEncodeBHist h

def dirichletApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletApproximationDecodeBHist tail)

private theorem dirichletApproximation_decode_encode :
    ∀ h : BHist,
      dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dirichletApproximationFields : DirichletApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletApproximationUp.mk Q B M D S G R E H C P N =>
      [Q, B, M, D, S, G, R, E, H, C, P, N]

def dirichletApproximationToEventFlow : DirichletApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletApproximationUp.mk Q B M D S G R E H C P N =>
      [[BMark.b0],
        dirichletApproximationEncodeBHist Q,
        [BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dirichletApproximationEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dirichletApproximationEncodeBHist N]

def dirichletApproximationFromEventFlow :
    EventFlow → Option DirichletApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] =>
      none
  | _tagQ :: Q :: _tagB :: B :: _tagM :: M :: _tagD :: D :: _tagS :: S :: _tagG ::
      G :: _tagR :: R :: _tagE :: E :: _tagH :: H :: _tagC :: C :: _tagP :: P ::
        _tagN :: N :: [] =>
      some (DirichletApproximationUp.mk
        (dirichletApproximationDecodeBHist Q) (dirichletApproximationDecodeBHist B)
        (dirichletApproximationDecodeBHist M) (dirichletApproximationDecodeBHist D)
        (dirichletApproximationDecodeBHist S) (dirichletApproximationDecodeBHist G)
        (dirichletApproximationDecodeBHist R) (dirichletApproximationDecodeBHist E)
        (dirichletApproximationDecodeBHist H) (dirichletApproximationDecodeBHist C)
        (dirichletApproximationDecodeBHist P) (dirichletApproximationDecodeBHist N))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
      none

private theorem dirichletApproximation_round_trip (x : DirichletApproximationUp) :
    dirichletApproximationFromEventFlow (dirichletApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q B M D S G R E H C P N =>
      change
        some
          (DirichletApproximationUp.mk
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist Q))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist B))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist M))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist D))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist S))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist G))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist R))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist E))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist H))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist C))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist P))
            (dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist N))) =
          some (DirichletApproximationUp.mk Q B M D S G R E H C P N)
      rw [dirichletApproximation_decode_encode Q, dirichletApproximation_decode_encode B,
        dirichletApproximation_decode_encode M, dirichletApproximation_decode_encode D,
        dirichletApproximation_decode_encode S, dirichletApproximation_decode_encode G,
        dirichletApproximation_decode_encode R, dirichletApproximation_decode_encode E,
        dirichletApproximation_decode_encode H, dirichletApproximation_decode_encode C,
        dirichletApproximation_decode_encode P, dirichletApproximation_decode_encode N]

private theorem dirichletApproximationToEventFlow_injective
    {x y : DirichletApproximationUp} :
    dirichletApproximationToEventFlow x = dirichletApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk Q1 B1 M1 D1 S1 G1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 B2 M2 D2 S2 G2 R2 E2 H2 C2 P2 N2 =>
          injection heq with _ htail0
          injection htail0 with hQ htail1
          injection htail1 with _ htail2
          injection htail2 with hB htail3
          injection htail3 with _ htail4
          injection htail4 with hM htail5
          injection htail5 with _ htail6
          injection htail6 with hD htail7
          injection htail7 with _ htail8
          injection htail8 with hS htail9
          injection htail9 with _ htail10
          injection htail10 with hG htail11
          injection htail11 with _ htail12
          injection htail12 with hR htail13
          injection htail13 with _ htail14
          injection htail14 with hE htail15
          injection htail15 with _ htail16
          injection htail16 with hH htail17
          injection htail17 with _ htail18
          injection htail18 with hC htail19
          injection htail19 with _ htail20
          injection htail20 with hP htail21
          injection htail21 with _ htail22
          injection htail22 with hN _
          have hQ' : Q1 = Q2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hQ
            exact Eq.trans (dirichletApproximation_decode_encode Q1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode Q2))
          cases hQ'
          have hB' : B1 = B2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hB
            exact Eq.trans (dirichletApproximation_decode_encode B1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode B2))
          cases hB'
          have hM' : M1 = M2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hM
            exact Eq.trans (dirichletApproximation_decode_encode M1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode M2))
          cases hM'
          have hD' : D1 = D2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hD
            exact Eq.trans (dirichletApproximation_decode_encode D1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode D2))
          cases hD'
          have hS' : S1 = S2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hS
            exact Eq.trans (dirichletApproximation_decode_encode S1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode S2))
          cases hS'
          have hG' : G1 = G2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hG
            exact Eq.trans (dirichletApproximation_decode_encode G1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode G2))
          cases hG'
          have hR' : R1 = R2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hR
            exact Eq.trans (dirichletApproximation_decode_encode R1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode R2))
          cases hR'
          have hE' : E1 = E2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hE
            exact Eq.trans (dirichletApproximation_decode_encode E1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode E2))
          cases hE'
          have hH' : H1 = H2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hH
            exact Eq.trans (dirichletApproximation_decode_encode H1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode H2))
          cases hH'
          have hC' : C1 = C2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hC
            exact Eq.trans (dirichletApproximation_decode_encode C1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode C2))
          cases hC'
          have hP' : P1 = P2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hP
            exact Eq.trans (dirichletApproximation_decode_encode P1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode P2))
          cases hP'
          have hN' : N1 = N2 := by
            have decoded := congrArg dirichletApproximationDecodeBHist hN
            exact Eq.trans (dirichletApproximation_decode_encode N1).symm
              (Eq.trans decoded (dirichletApproximation_decode_encode N2))
          cases hN'
          rfl

instance dirichletApproximationBHistCarrier : BHistCarrier DirichletApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletApproximationToEventFlow
  fromEventFlow := dirichletApproximationFromEventFlow

instance dirichletApproximationChapterTasteGate :
    ChapterTasteGate DirichletApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dirichletApproximationFromEventFlow (dirichletApproximationToEventFlow x) =
      some x
    exact dirichletApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dirichletApproximationToEventFlow_injective heq)

instance dirichletApproximationFieldFaithful :
    FieldFaithful DirichletApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dirichletApproximationFields
  field_faithful := by
    intro x y h
    cases x with
    | mk Q1 B1 M1 D1 S1 G1 R1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk Q2 B2 M2 D2 S2 G2 R2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

instance dirichletApproximationNontrivial : Nontrivial DirichletApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DirichletApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DirichletApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DirichletApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dirichletApproximationChapterTasteGate

theorem DirichletApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DirichletApproximationUp) ∧
      Nonempty (FieldFaithful DirichletApproximationUp) ∧
        Nonempty (Nontrivial DirichletApproximationUp) ∧
          (∀ h : BHist,
            dirichletApproximationDecodeBHist (dirichletApproximationEncodeBHist h) = h) ∧
            (∀ x : DirichletApproximationUp,
              dirichletApproximationFromEventFlow (dirichletApproximationToEventFlow x) =
                some x) ∧
              dirichletApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨dirichletApproximationChapterTasteGate⟩
  · constructor
    · exact ⟨dirichletApproximationFieldFaithful⟩
    · constructor
      · exact ⟨dirichletApproximationNontrivial⟩
      · constructor
        · exact dirichletApproximation_decode_encode
        · constructor
          · exact dirichletApproximation_round_trip
          · rfl

end BEDC.Derived.DirichletApproximationUp
