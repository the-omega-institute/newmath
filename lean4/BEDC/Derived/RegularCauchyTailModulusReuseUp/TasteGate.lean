import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailModulusReuseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailModulusReuseUp : Type where
  | mk (S Q T E L W D M U H C P N : BHist) : RegularCauchyTailModulusReuseUp
  deriving DecidableEq

def regularCauchyTailModulusReuseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailModulusReuseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailModulusReuseEncodeBHist h

def regularCauchyTailModulusReuseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailModulusReuseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailModulusReuseDecodeBHist tail)

private theorem regularCauchyTailModulusReuseDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailModulusReuseFields :
    RegularCauchyTailModulusReuseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailModulusReuseUp.mk S Q T E L W D M U H C P N =>
      [S, Q, T, E, L, W, D, M, U, H, C, P, N]

def regularCauchyTailModulusReuseToEventFlow :
    RegularCauchyTailModulusReuseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailModulusReuseFields x).map
      regularCauchyTailModulusReuseEncodeBHist

def regularCauchyTailModulusReuseFromEventFlow :
    EventFlow → Option RegularCauchyTailModulusReuseUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l :: [] =>
      none
  | S :: Q :: T :: E :: L :: W :: D :: M :: U :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyTailModulusReuseUp.mk
          (regularCauchyTailModulusReuseDecodeBHist S)
          (regularCauchyTailModulusReuseDecodeBHist Q)
          (regularCauchyTailModulusReuseDecodeBHist T)
          (regularCauchyTailModulusReuseDecodeBHist E)
          (regularCauchyTailModulusReuseDecodeBHist L)
          (regularCauchyTailModulusReuseDecodeBHist W)
          (regularCauchyTailModulusReuseDecodeBHist D)
          (regularCauchyTailModulusReuseDecodeBHist M)
          (regularCauchyTailModulusReuseDecodeBHist U)
          (regularCauchyTailModulusReuseDecodeBHist H)
          (regularCauchyTailModulusReuseDecodeBHist C)
          (regularCauchyTailModulusReuseDecodeBHist P)
          (regularCauchyTailModulusReuseDecodeBHist N))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k ::
      _l :: _m :: _n :: _rest => none

private theorem regularCauchyTailModulusReuse_round_trip :
    ∀ x : RegularCauchyTailModulusReuseUp,
      regularCauchyTailModulusReuseFromEventFlow
        (regularCauchyTailModulusReuseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q T E L W D M U H C P N =>
      change
        some
          (RegularCauchyTailModulusReuseUp.mk
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist S))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist Q))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist T))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist E))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist L))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist W))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist D))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist M))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist U))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist H))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist C))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist P))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist N))) =
          some (RegularCauchyTailModulusReuseUp.mk S Q T E L W D M U H C P N)
      rw [regularCauchyTailModulusReuseDecode_encode_bhist S,
        regularCauchyTailModulusReuseDecode_encode_bhist Q,
        regularCauchyTailModulusReuseDecode_encode_bhist T,
        regularCauchyTailModulusReuseDecode_encode_bhist E,
        regularCauchyTailModulusReuseDecode_encode_bhist L,
        regularCauchyTailModulusReuseDecode_encode_bhist W,
        regularCauchyTailModulusReuseDecode_encode_bhist D,
        regularCauchyTailModulusReuseDecode_encode_bhist M,
        regularCauchyTailModulusReuseDecode_encode_bhist U,
        regularCauchyTailModulusReuseDecode_encode_bhist H,
        regularCauchyTailModulusReuseDecode_encode_bhist C,
        regularCauchyTailModulusReuseDecode_encode_bhist P,
        regularCauchyTailModulusReuseDecode_encode_bhist N]

private theorem regularCauchyTailModulusReuseToEventFlow_injective
    {x y : RegularCauchyTailModulusReuseUp} :
    regularCauchyTailModulusReuseToEventFlow x =
      regularCauchyTailModulusReuseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow x) =
        regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow y) :=
    congrArg regularCauchyTailModulusReuseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailModulusReuse_round_trip x).symm
      (Eq.trans hread (regularCauchyTailModulusReuse_round_trip y)))

private theorem regularCauchyTailModulusReuse_fields_faithful :
    ∀ x y : RegularCauchyTailModulusReuseUp,
      regularCauchyTailModulusReuseFields x =
        regularCauchyTailModulusReuseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S Q T E L W D M U H C P N =>
      cases y with
      | mk S' Q' T' E' L' W' D' M' U' H' C' P' N' =>
          cases hfields
          rfl

instance regularCauchyTailModulusReuseBHistCarrier :
    BHistCarrier RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailModulusReuseToEventFlow
  fromEventFlow := regularCauchyTailModulusReuseFromEventFlow

instance regularCauchyTailModulusReuseChapterTasteGate :
    ChapterTasteGate RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailModulusReuseFromEventFlow
        (regularCauchyTailModulusReuseToEventFlow x) = some x
    exact regularCauchyTailModulusReuse_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailModulusReuseToEventFlow_injective heq)

instance regularCauchyTailModulusReuseFieldFaithful :
    FieldFaithful RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailModulusReuseFields
  field_faithful := regularCauchyTailModulusReuse_fields_faithful

instance regularCauchyTailModulusReuseNontrivial :
    Nontrivial RegularCauchyTailModulusReuseUp where
  witness_pair :=
    ⟨RegularCauchyTailModulusReuseUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailModulusReuseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailModulusReuseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailModulusReuseChapterTasteGate

theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyTailModulusReuseDecodeBHist
          (regularCauchyTailModulusReuseEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailModulusReuseUp,
        regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyTailModulusReuseUp,
        regularCauchyTailModulusReuseToEventFlow x =
          regularCauchyTailModulusReuseToEventFlow y → x = y) ∧
      regularCauchyTailModulusReuseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨regularCauchyTailModulusReuseDecode_encode_bhist,
    regularCauchyTailModulusReuse_round_trip,
    fun _ _ heq => regularCauchyTailModulusReuseToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.RegularCauchyTailModulusReuseUp
