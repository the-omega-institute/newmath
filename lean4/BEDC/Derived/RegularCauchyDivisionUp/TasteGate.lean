import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDivisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDivisionUp : Type where
  | mk (X Y A I P W R E H C Q N : BHist) : RegularCauchyDivisionUp
  deriving DecidableEq

def regularCauchyDivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDivisionEncodeBHist h

def regularCauchyDivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDivisionDecodeBHist tail)

private theorem regularCauchyDivisionDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyDivision_mk_congr
    {X X' Y Y' A A' I I' P P' W W' R R' E E' H H' C C' Q Q' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hA : A' = A) (hI : I' = I) (hP : P' = P)
    (hW : W' = W) (hR : R' = R) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hQ : Q' = Q) (hN : N' = N) :
    RegularCauchyDivisionUp.mk X' Y' A' I' P' W' R' E' H' C' Q' N' =
      RegularCauchyDivisionUp.mk X Y A I P W R E H C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hA
  cases hI
  cases hP
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def regularCauchyDivisionFields : RegularCauchyDivisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDivisionUp.mk X Y A I P W R E H C Q N =>
      [X, Y, A, I, P, W, R, E, H, C, Q, N]

def regularCauchyDivisionToEventFlow : RegularCauchyDivisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyDivisionFields x).map regularCauchyDivisionEncodeBHist

def regularCauchyDivisionFromEventFlow :
    EventFlow → Option RegularCauchyDivisionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _Y :: [] => none
  | _X :: _Y :: _A :: [] => none
  | _X :: _Y :: _A :: _I :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: _E :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: _E :: _H :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: _E :: _H :: _C :: [] => none
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: _E :: _H :: _C :: _Q :: [] => none
  | X :: Y :: A :: I :: P :: W :: R :: E :: H :: C :: Q :: N :: [] =>
      some
        (RegularCauchyDivisionUp.mk
          (regularCauchyDivisionDecodeBHist X)
          (regularCauchyDivisionDecodeBHist Y)
          (regularCauchyDivisionDecodeBHist A)
          (regularCauchyDivisionDecodeBHist I)
          (regularCauchyDivisionDecodeBHist P)
          (regularCauchyDivisionDecodeBHist W)
          (regularCauchyDivisionDecodeBHist R)
          (regularCauchyDivisionDecodeBHist E)
          (regularCauchyDivisionDecodeBHist H)
          (regularCauchyDivisionDecodeBHist C)
          (regularCauchyDivisionDecodeBHist Q)
          (regularCauchyDivisionDecodeBHist N))
  | _X :: _Y :: _A :: _I :: _P :: _W :: _R :: _E :: _H :: _C :: _Q :: _N ::
      _extra :: _rest => none

private theorem regularCauchyDivision_round_trip :
    ∀ x : RegularCauchyDivisionUp,
      regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y A I P W R E H C Q N =>
      exact
        congrArg some
          (regularCauchyDivision_mk_congr
            (regularCauchyDivisionDecode_encode_bhist X)
            (regularCauchyDivisionDecode_encode_bhist Y)
            (regularCauchyDivisionDecode_encode_bhist A)
            (regularCauchyDivisionDecode_encode_bhist I)
            (regularCauchyDivisionDecode_encode_bhist P)
            (regularCauchyDivisionDecode_encode_bhist W)
            (regularCauchyDivisionDecode_encode_bhist R)
            (regularCauchyDivisionDecode_encode_bhist E)
            (regularCauchyDivisionDecode_encode_bhist H)
            (regularCauchyDivisionDecode_encode_bhist C)
            (regularCauchyDivisionDecode_encode_bhist Q)
            (regularCauchyDivisionDecode_encode_bhist N))

private theorem regularCauchyDivisionToEventFlow_injective
    {x y : RegularCauchyDivisionUp} :
    regularCauchyDivisionToEventFlow x = regularCauchyDivisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) =
        regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow y) :=
    congrArg regularCauchyDivisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDivision_round_trip x).symm
      (Eq.trans hread (regularCauchyDivision_round_trip y)))

private theorem regularCauchyDivision_field_faithful :
    ∀ x y : RegularCauchyDivisionUp,
      regularCauchyDivisionFields x = regularCauchyDivisionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X Y A I P W R E H C Q N =>
      cases y with
      | mk X' Y' A' I' P' W' R' E' H' C' Q' N' =>
          cases hfields
          rfl

instance regularCauchyDivisionBHistCarrier : BHistCarrier RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDivisionToEventFlow
  fromEventFlow := regularCauchyDivisionFromEventFlow

instance regularCauchyDivisionChapterTasteGate :
    ChapterTasteGate RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDivisionFromEventFlow
      (regularCauchyDivisionToEventFlow x) = some x
    exact regularCauchyDivision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDivisionToEventFlow_injective heq)

instance regularCauchyDivisionFieldFaithful : FieldFaithful RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyDivisionFields
  field_faithful := regularCauchyDivision_field_faithful

instance regularCauchyDivisionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyDivisionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyDivisionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyDivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDivisionChapterTasteGate

theorem RegularCauchyDivisionTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyDivisionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact regularCauchyDivisionChapterTasteGate

end BEDC.Derived.RegularCauchyDivisionUp
