import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScientificObjectUp : Type where
  | mk : (R K I L B G A T O D H C P N : BHist) → ScientificObjectUp
  deriving DecidableEq

def scientificObjectEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scientificObjectEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scientificObjectEncodeBHist h

def scientificObjectDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scientificObjectDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scientificObjectDecodeBHist tail)

private theorem scientificObject_decode_encode_bhist :
    ∀ h : BHist, scientificObjectDecodeBHist (scientificObjectEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem scientificObject_mk_congr
    {R R' K K' I I' L L' B B' G G' A A' T T' O O' D D' H H' C C' P P' N N' :
      BHist}
    (hR : R' = R) (hK : K' = K) (hI : I' = I) (hL : L' = L) (hB : B' = B)
    (hG : G' = G) (hA : A' = A) (hT : T' = T) (hO : O' = O) (hD : D' = D)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ScientificObjectUp.mk R' K' I' L' B' G' A' T' O' D' H' C' P' N' =
      ScientificObjectUp.mk R K I L B G A T O D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hK
  cases hI
  cases hL
  cases hB
  cases hG
  cases hA
  cases hT
  cases hO
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def scientificObjectFields : ScientificObjectUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScientificObjectUp.mk R K I L B G A T O D H C P N =>
      [R, K, I, L, B, G, A, T, O, D, H, C, P, N]

def scientificObjectToEventFlow : ScientificObjectUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (scientificObjectFields x).map scientificObjectEncodeBHist

def scientificObjectFromEventFlow : EventFlow → Option ScientificObjectUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _R :: [] => none
  | _R :: _K :: [] => none
  | _R :: _K :: _I :: [] => none
  | _R :: _K :: _I :: _L :: [] => none
  | _R :: _K :: _I :: _L :: _B :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: _D :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: _D :: _H :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: _D :: _H :: _C :: [] => none
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: _D :: _H :: _C :: _P :: [] =>
      none
  | R :: K :: I :: L :: B :: G :: A :: T :: O :: D :: H :: C :: P :: N :: [] =>
      some
        (ScientificObjectUp.mk
          (scientificObjectDecodeBHist R)
          (scientificObjectDecodeBHist K)
          (scientificObjectDecodeBHist I)
          (scientificObjectDecodeBHist L)
          (scientificObjectDecodeBHist B)
          (scientificObjectDecodeBHist G)
          (scientificObjectDecodeBHist A)
          (scientificObjectDecodeBHist T)
          (scientificObjectDecodeBHist O)
          (scientificObjectDecodeBHist D)
          (scientificObjectDecodeBHist H)
          (scientificObjectDecodeBHist C)
          (scientificObjectDecodeBHist P)
          (scientificObjectDecodeBHist N))
  | _R :: _K :: _I :: _L :: _B :: _G :: _A :: _T :: _O :: _D :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem scientificObject_round_trip :
    ∀ x : ScientificObjectUp,
      scientificObjectFromEventFlow (scientificObjectToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R K I L B G A T O D H C P N =>
      exact
        congrArg some
          (scientificObject_mk_congr
            (scientificObject_decode_encode_bhist R)
            (scientificObject_decode_encode_bhist K)
            (scientificObject_decode_encode_bhist I)
            (scientificObject_decode_encode_bhist L)
            (scientificObject_decode_encode_bhist B)
            (scientificObject_decode_encode_bhist G)
            (scientificObject_decode_encode_bhist A)
            (scientificObject_decode_encode_bhist T)
            (scientificObject_decode_encode_bhist O)
            (scientificObject_decode_encode_bhist D)
            (scientificObject_decode_encode_bhist H)
            (scientificObject_decode_encode_bhist C)
            (scientificObject_decode_encode_bhist P)
            (scientificObject_decode_encode_bhist N))

private theorem scientificObjectToEventFlow_injective {x y : ScientificObjectUp} :
    scientificObjectToEventFlow x = scientificObjectToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scientificObjectFromEventFlow (scientificObjectToEventFlow x) =
        scientificObjectFromEventFlow (scientificObjectToEventFlow y) :=
    congrArg scientificObjectFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (scientificObject_round_trip x).symm
      (Eq.trans hread (scientificObject_round_trip y)))

private theorem scientificObject_field_faithful :
    ∀ x y : ScientificObjectUp, scientificObjectFields x = scientificObjectFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R K I L B G A T O D H C P N =>
      cases y with
      | mk R' K' I' L' B' G' A' T' O' D' H' C' P' N' =>
          cases hfields
          rfl

instance scientificObjectBHistCarrier : BHistCarrier ScientificObjectUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scientificObjectToEventFlow
  fromEventFlow := scientificObjectFromEventFlow

instance scientificObjectChapterTasteGate : ChapterTasteGate ScientificObjectUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scientificObjectFromEventFlow (scientificObjectToEventFlow x) = some x
    exact scientificObject_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (scientificObjectToEventFlow_injective heq)

instance scientificObjectFieldFaithful : FieldFaithful ScientificObjectUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := scientificObjectFields
  field_faithful := scientificObject_field_faithful

instance scientificObjectNontrivial : BEDC.Meta.TasteGate.Nontrivial ScientificObjectUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ScientificObjectUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ScientificObjectUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ScientificObjectUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scientificObjectChapterTasteGate

theorem ScientificObjectUp_single_carrier_alignment :
    Nonempty (ChapterTasteGate ScientificObjectUp) ∧ Nonempty (BHistCarrier ScientificObjectUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨scientificObjectChapterTasteGate⟩, ⟨scientificObjectBHistCarrier⟩⟩

end BEDC.Derived.ScientificObjectUp
