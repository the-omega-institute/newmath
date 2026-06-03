import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedClosedBallUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedClosedBallUp : Type where
  | mk (M c r D I R E H C P N : BHist) : LocatedClosedBallUp
  deriving DecidableEq

def locatedClosedBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedClosedBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedClosedBallEncodeBHist h

def locatedClosedBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedClosedBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedClosedBallDecodeBHist tail)

private theorem locatedClosedBallDecode_encode_bhist :
    ∀ h : BHist,
      locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedClosedBallFields : LocatedClosedBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedClosedBallUp.mk M c r D I R E H C P N =>
      [M, c, r, D, I, R, E, H, C, P, N]

def locatedClosedBallToEventFlow : LocatedClosedBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedClosedBallFields x).map locatedClosedBallEncodeBHist

def locatedClosedBallFromEventFlow : EventFlow → LocatedClosedBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: _R :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: _P :: [] =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  | M :: c :: r :: D :: I :: R :: E :: H :: C :: P :: N :: [] =>
      LocatedClosedBallUp.mk
        (locatedClosedBallDecodeBHist M)
        (locatedClosedBallDecodeBHist c)
        (locatedClosedBallDecodeBHist r)
        (locatedClosedBallDecodeBHist D)
        (locatedClosedBallDecodeBHist I)
        (locatedClosedBallDecodeBHist R)
        (locatedClosedBallDecodeBHist E)
        (locatedClosedBallDecodeBHist H)
        (locatedClosedBallDecodeBHist C)
        (locatedClosedBallDecodeBHist P)
        (locatedClosedBallDecodeBHist N)
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

def locatedClosedBallFromEventFlowOption : EventFlow → Option LocatedClosedBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _M :: [] => none
  | _M :: _c :: [] => none
  | _M :: _c :: _r :: [] => none
  | _M :: _c :: _r :: _D :: [] => none
  | _M :: _c :: _r :: _D :: _I :: [] => none
  | _M :: _c :: _r :: _D :: _I :: _R :: [] => none
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: [] => none
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: [] => none
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: [] => none
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: _P :: [] => none
  | M :: c :: r :: D :: I :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (LocatedClosedBallUp.mk
          (locatedClosedBallDecodeBHist M)
          (locatedClosedBallDecodeBHist c)
          (locatedClosedBallDecodeBHist r)
          (locatedClosedBallDecodeBHist D)
          (locatedClosedBallDecodeBHist I)
          (locatedClosedBallDecodeBHist R)
          (locatedClosedBallDecodeBHist E)
          (locatedClosedBallDecodeBHist H)
          (locatedClosedBallDecodeBHist C)
          (locatedClosedBallDecodeBHist P)
          (locatedClosedBallDecodeBHist N))
  | _M :: _c :: _r :: _D :: _I :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem locatedClosedBall_round_trip :
    ∀ x : LocatedClosedBallUp,
      locatedClosedBallFromEventFlow (locatedClosedBallToEventFlow x) = x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M c r D I R E H C P N =>
      change
        LocatedClosedBallUp.mk
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist M))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist c))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist r))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist D))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist I))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist R))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist E))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist H))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist C))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist P))
            (locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist N)) =
          LocatedClosedBallUp.mk M c r D I R E H C P N
      rw [locatedClosedBallDecode_encode_bhist M,
        locatedClosedBallDecode_encode_bhist c,
        locatedClosedBallDecode_encode_bhist r,
        locatedClosedBallDecode_encode_bhist D,
        locatedClosedBallDecode_encode_bhist I,
        locatedClosedBallDecode_encode_bhist R,
        locatedClosedBallDecode_encode_bhist E,
        locatedClosedBallDecode_encode_bhist H,
        locatedClosedBallDecode_encode_bhist C,
        locatedClosedBallDecode_encode_bhist P,
        locatedClosedBallDecode_encode_bhist N]

private theorem locatedClosedBall_option_round_trip :
    ∀ x : LocatedClosedBallUp,
      locatedClosedBallFromEventFlowOption (locatedClosedBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M c r D I R E H C P N =>
      change
        some
            (locatedClosedBallFromEventFlow
              [locatedClosedBallEncodeBHist M, locatedClosedBallEncodeBHist c,
                locatedClosedBallEncodeBHist r, locatedClosedBallEncodeBHist D,
                locatedClosedBallEncodeBHist I, locatedClosedBallEncodeBHist R,
                locatedClosedBallEncodeBHist E, locatedClosedBallEncodeBHist H,
                locatedClosedBallEncodeBHist C, locatedClosedBallEncodeBHist P,
                locatedClosedBallEncodeBHist N]) =
          some (LocatedClosedBallUp.mk M c r D I R E H C P N)
      exact congrArg some (locatedClosedBall_round_trip
        (LocatedClosedBallUp.mk M c r D I R E H C P N))

private theorem locatedClosedBallToEventFlow_injective
    {x y : LocatedClosedBallUp} :
    locatedClosedBallToEventFlow x = locatedClosedBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedClosedBallFromEventFlowOption (locatedClosedBallToEventFlow x) =
        locatedClosedBallFromEventFlowOption (locatedClosedBallToEventFlow y) :=
    congrArg locatedClosedBallFromEventFlowOption heq
  exact Option.some.inj
    (Eq.trans (locatedClosedBall_option_round_trip x).symm
      (Eq.trans hread (locatedClosedBall_option_round_trip y)))

private theorem locatedClosedBall_fields_faithful :
    ∀ x y : LocatedClosedBallUp,
      locatedClosedBallFields x = locatedClosedBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M c r D I R E H C P N =>
      cases y with
      | mk M' c' r' D' I' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance locatedClosedBallBHistCarrier : BHistCarrier LocatedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedClosedBallToEventFlow
  fromEventFlow := locatedClosedBallFromEventFlowOption

instance locatedClosedBallChapterTasteGate :
    ChapterTasteGate LocatedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := locatedClosedBall_option_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedClosedBallToEventFlow_injective heq)

instance locatedClosedBallFieldFaithful : FieldFaithful LocatedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedClosedBallFields
  field_faithful := locatedClosedBall_fields_faithful

instance locatedClosedBallNontrivial : Nontrivial LocatedClosedBallUp where
  witness_pair :=
    ⟨LocatedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedClosedBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedClosedBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedClosedBallChapterTasteGate

theorem LocatedClosedBallTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedClosedBallDecodeBHist (locatedClosedBallEncodeBHist h) = h) ∧
      (∀ x : LocatedClosedBallUp,
        locatedClosedBallFromEventFlowOption (locatedClosedBallToEventFlow x) = some x) ∧
        (∀ x y : LocatedClosedBallUp,
          locatedClosedBallToEventFlow x = locatedClosedBallToEventFlow y → x = y) ∧
          locatedClosedBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨locatedClosedBallDecode_encode_bhist,
      locatedClosedBall_option_round_trip,
      (fun _ _ heq => locatedClosedBallToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedClosedBallUp.TasteGate
