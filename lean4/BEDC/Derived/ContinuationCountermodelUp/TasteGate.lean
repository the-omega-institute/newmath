import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationCountermodelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationCountermodelUp : Type where
  | mk : (F U M O K S E H R P N : BHist) → ContinuationCountermodelUp
  deriving DecidableEq

def continuationCountermodelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationCountermodelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationCountermodelEncodeBHist h

def continuationCountermodelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationCountermodelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationCountermodelDecodeBHist tail)

private theorem continuationCountermodelDecode_encode_bhist :
    ∀ h : BHist,
      continuationCountermodelDecodeBHist
        (continuationCountermodelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem continuationCountermodel_mk_congr
    {F F' U U' M M' O O' K K' S S' E E' H H' R R' P P' N N' : BHist}
    (hF : F' = F) (hU : U' = U) (hM : M' = M) (hO : O' = O) (hK : K' = K)
    (hS : S' = S) (hE : E' = E) (hH : H' = H) (hR : R' = R) (hP : P' = P)
    (hN : N' = N) :
    ContinuationCountermodelUp.mk F' U' M' O' K' S' E' H' R' P' N' =
      ContinuationCountermodelUp.mk F U M O K S E H R P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hU
  cases hM
  cases hO
  cases hK
  cases hS
  cases hE
  cases hH
  cases hR
  cases hP
  cases hN
  rfl

def continuationCountermodelFields :
    ContinuationCountermodelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationCountermodelUp.mk F U M O K S E H R P N =>
      [F, U, M, O, K, S, E, H, R, P, N]

def continuationCountermodelToEventFlow :
    ContinuationCountermodelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuationCountermodelFields x).map continuationCountermodelEncodeBHist

def continuationCountermodelFromEventFlow :
    EventFlow → Option ContinuationCountermodelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _F :: [] => none
  | _F :: _U :: [] => none
  | _F :: _U :: _M :: [] => none
  | _F :: _U :: _M :: _O :: [] => none
  | _F :: _U :: _M :: _O :: _K :: [] => none
  | _F :: _U :: _M :: _O :: _K :: _S :: [] => none
  | _F :: _U :: _M :: _O :: _K :: _S :: _E :: [] => none
  | _F :: _U :: _M :: _O :: _K :: _S :: _E :: _H :: [] => none
  | _F :: _U :: _M :: _O :: _K :: _S :: _E :: _H :: _R :: [] => none
  | _F :: _U :: _M :: _O :: _K :: _S :: _E :: _H :: _R :: _P :: [] => none
  | F :: U :: M :: O :: K :: S :: E :: H :: R :: P :: N :: [] =>
      some
        (ContinuationCountermodelUp.mk
          (continuationCountermodelDecodeBHist F)
          (continuationCountermodelDecodeBHist U)
          (continuationCountermodelDecodeBHist M)
          (continuationCountermodelDecodeBHist O)
          (continuationCountermodelDecodeBHist K)
          (continuationCountermodelDecodeBHist S)
          (continuationCountermodelDecodeBHist E)
          (continuationCountermodelDecodeBHist H)
          (continuationCountermodelDecodeBHist R)
          (continuationCountermodelDecodeBHist P)
          (continuationCountermodelDecodeBHist N))
  | _F :: _U :: _M :: _O :: _K :: _S :: _E :: _H :: _R :: _P :: _N :: _extra :: _rest =>
      none

private theorem continuationCountermodel_round_trip :
    ∀ x : ContinuationCountermodelUp,
      continuationCountermodelFromEventFlow
        (continuationCountermodelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U M O K S E H R P N =>
      exact
        congrArg some
          (continuationCountermodel_mk_congr
            (continuationCountermodelDecode_encode_bhist F)
            (continuationCountermodelDecode_encode_bhist U)
            (continuationCountermodelDecode_encode_bhist M)
            (continuationCountermodelDecode_encode_bhist O)
            (continuationCountermodelDecode_encode_bhist K)
            (continuationCountermodelDecode_encode_bhist S)
            (continuationCountermodelDecode_encode_bhist E)
            (continuationCountermodelDecode_encode_bhist H)
            (continuationCountermodelDecode_encode_bhist R)
            (continuationCountermodelDecode_encode_bhist P)
            (continuationCountermodelDecode_encode_bhist N))

private theorem continuationCountermodelToEventFlow_injective
    {x y : ContinuationCountermodelUp} :
    continuationCountermodelToEventFlow x =
      continuationCountermodelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationCountermodelFromEventFlow
          (continuationCountermodelToEventFlow x) =
        continuationCountermodelFromEventFlow
          (continuationCountermodelToEventFlow y) :=
    congrArg continuationCountermodelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationCountermodel_round_trip x).symm
      (Eq.trans hread (continuationCountermodel_round_trip y)))

private theorem continuationCountermodel_field_faithful :
    ∀ x y : ContinuationCountermodelUp,
      continuationCountermodelFields x =
        continuationCountermodelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F U M O K S E H R P N =>
      cases y with
      | mk F' U' M' O' K' S' E' H' R' P' N' =>
          cases hfields
          rfl

instance continuationCountermodelBHistCarrier :
    BHistCarrier ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationCountermodelToEventFlow
  fromEventFlow := continuationCountermodelFromEventFlow

instance continuationCountermodelChapterTasteGate :
    ChapterTasteGate ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuationCountermodelFromEventFlow
        (continuationCountermodelToEventFlow x) = some x
    exact continuationCountermodel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationCountermodelToEventFlow_injective heq)

instance continuationCountermodelFieldFaithful :
    FieldFaithful ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuationCountermodelFields
  field_faithful := continuationCountermodel_field_faithful

instance continuationCountermodelNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationCountermodelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuationCountermodelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContinuationCountermodelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationCountermodelChapterTasteGate

theorem ContinuationCountermodelTasteGate_single_carrier_alignment :
    (∀ h : BHist, continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist h) = h) ∧
      (∀ x : ContinuationCountermodelUp,
        continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) = some x) ∧
        (∀ x y : ContinuationCountermodelUp,
          continuationCountermodelToEventFlow x = continuationCountermodelToEventFlow y → x = y) ∧
          continuationCountermodelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨continuationCountermodelDecode_encode_bhist,
      continuationCountermodel_round_trip,
      (fun _ _ heq => continuationCountermodelToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuationCountermodelUp
