import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObjectConstitutionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObjectConstitutionLedgerUp : Type where
  | mk : (F I E R S A K L G H C P N : BHist) → ObjectConstitutionLedgerUp
  deriving DecidableEq

def objectConstitutionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: objectConstitutionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: objectConstitutionLedgerEncodeBHist h

def objectConstitutionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (objectConstitutionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (objectConstitutionLedgerDecodeBHist tail)

private theorem objectConstitutionLedgerDecode_encode_bhist :
    ∀ h : BHist,
      objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem objectConstitutionLedger_mk_congr
    {F F' I I' E E' R R' S S' A A' K K' L L' G G' H H' C C' P P' N N' : BHist}
    (hF : F' = F) (hI : I' = I) (hE : E' = E) (hR : R' = R) (hS : S' = S)
    (hA : A' = A) (hK : K' = K) (hL : L' = L) (hG : G' = G) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ObjectConstitutionLedgerUp.mk F' I' E' R' S' A' K' L' G' H' C' P' N' =
      ObjectConstitutionLedgerUp.mk F I E R S A K L G H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hI
  cases hE
  cases hR
  cases hS
  cases hA
  cases hK
  cases hL
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def objectConstitutionLedgerFields :
    ObjectConstitutionLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectConstitutionLedgerUp.mk F I E R S A K L G H C P N =>
      [F, I, E, R, S, A, K, L, G, H, C, P, N]

def objectConstitutionLedgerToEventFlow :
    ObjectConstitutionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (objectConstitutionLedgerFields x).map objectConstitutionLedgerEncodeBHist

def objectConstitutionLedgerFromEventFlow :
    EventFlow → Option ObjectConstitutionLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _F :: [] => none
  | _F :: _I :: [] => none
  | _F :: _I :: _E :: [] => none
  | _F :: _I :: _E :: _R :: [] => none
  | _F :: _I :: _E :: _R :: _S :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: _G :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: _G :: _H :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: _G :: _H :: _C :: [] => none
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: _G :: _H :: _C :: _P :: [] => none
  | F :: I :: E :: R :: S :: A :: K :: L :: G :: H :: C :: P :: N :: [] =>
      some
        (ObjectConstitutionLedgerUp.mk
          (objectConstitutionLedgerDecodeBHist F)
          (objectConstitutionLedgerDecodeBHist I)
          (objectConstitutionLedgerDecodeBHist E)
          (objectConstitutionLedgerDecodeBHist R)
          (objectConstitutionLedgerDecodeBHist S)
          (objectConstitutionLedgerDecodeBHist A)
          (objectConstitutionLedgerDecodeBHist K)
          (objectConstitutionLedgerDecodeBHist L)
          (objectConstitutionLedgerDecodeBHist G)
          (objectConstitutionLedgerDecodeBHist H)
          (objectConstitutionLedgerDecodeBHist C)
          (objectConstitutionLedgerDecodeBHist P)
          (objectConstitutionLedgerDecodeBHist N))
  | _F :: _I :: _E :: _R :: _S :: _A :: _K :: _L :: _G :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem objectConstitutionLedger_round_trip :
    ∀ x : ObjectConstitutionLedgerUp,
      objectConstitutionLedgerFromEventFlow (objectConstitutionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I E R S A K L G H C P N =>
      exact
        congrArg some
          (objectConstitutionLedger_mk_congr
            (objectConstitutionLedgerDecode_encode_bhist F)
            (objectConstitutionLedgerDecode_encode_bhist I)
            (objectConstitutionLedgerDecode_encode_bhist E)
            (objectConstitutionLedgerDecode_encode_bhist R)
            (objectConstitutionLedgerDecode_encode_bhist S)
            (objectConstitutionLedgerDecode_encode_bhist A)
            (objectConstitutionLedgerDecode_encode_bhist K)
            (objectConstitutionLedgerDecode_encode_bhist L)
            (objectConstitutionLedgerDecode_encode_bhist G)
            (objectConstitutionLedgerDecode_encode_bhist H)
            (objectConstitutionLedgerDecode_encode_bhist C)
            (objectConstitutionLedgerDecode_encode_bhist P)
            (objectConstitutionLedgerDecode_encode_bhist N))

private theorem objectConstitutionLedgerToEventFlow_injective
    {x y : ObjectConstitutionLedgerUp} :
    objectConstitutionLedgerToEventFlow x = objectConstitutionLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      objectConstitutionLedgerFromEventFlow (objectConstitutionLedgerToEventFlow x) =
        objectConstitutionLedgerFromEventFlow (objectConstitutionLedgerToEventFlow y) :=
    congrArg objectConstitutionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (objectConstitutionLedger_round_trip x).symm
      (Eq.trans hread (objectConstitutionLedger_round_trip y)))

private theorem objectConstitutionLedger_field_faithful :
    ∀ x y : ObjectConstitutionLedgerUp,
      objectConstitutionLedgerFields x = objectConstitutionLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F I E R S A K L G H C P N =>
      cases y with
      | mk F' I' E' R' S' A' K' L' G' H' C' P' N' =>
          cases hfields
          rfl

instance objectConstitutionLedgerBHistCarrier : BHistCarrier ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := objectConstitutionLedgerToEventFlow
  fromEventFlow := objectConstitutionLedgerFromEventFlow

instance objectConstitutionLedgerChapterTasteGate :
    ChapterTasteGate ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      objectConstitutionLedgerFromEventFlow (objectConstitutionLedgerToEventFlow x) = some x
    exact objectConstitutionLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (objectConstitutionLedgerToEventFlow_injective heq)

instance objectConstitutionLedgerFieldFaithful :
    FieldFaithful ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := objectConstitutionLedgerFields
  field_faithful := objectConstitutionLedger_field_faithful

instance objectConstitutionLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObjectConstitutionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObjectConstitutionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObjectConstitutionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  objectConstitutionLedgerChapterTasteGate

theorem ObjectConstitutionLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEncodeBHist h) = h) ∧
      (∀ x : ObjectConstitutionLedgerUp,
        objectConstitutionLedgerFromEventFlow (objectConstitutionLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : ObjectConstitutionLedgerUp,
          objectConstitutionLedgerToEventFlow x = objectConstitutionLedgerToEventFlow y →
            x = y) ∧
          objectConstitutionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨objectConstitutionLedgerDecode_encode_bhist,
      objectConstitutionLedger_round_trip,
      (fun _ _ heq => objectConstitutionLedgerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ObjectConstitutionLedgerUp
