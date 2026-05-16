import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketTaxonomyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketTaxonomyLedgerUp : Type where
  | mk : (K S A R D H C P N : BHist) → SocketTaxonomyLedgerUp
  deriving DecidableEq

def socketTaxonomyLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketTaxonomyLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketTaxonomyLedgerEncodeBHist h

def socketTaxonomyLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketTaxonomyLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketTaxonomyLedgerDecodeBHist tail)

private theorem socketTaxonomyLedgerDecode_encode_bhist :
    ∀ h : BHist,
      socketTaxonomyLedgerDecodeBHist (socketTaxonomyLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem socketTaxonomyLedger_mk_congr
    {K K' S S' A A' R R' D D' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hS : S' = S) (hA : A' = A) (hR : R' = R) (hD : D' = D)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    SocketTaxonomyLedgerUp.mk K' S' A' R' D' H' C' P' N' =
      SocketTaxonomyLedgerUp.mk K S A R D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hS
  cases hA
  cases hR
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def socketTaxonomyLedgerFields :
    SocketTaxonomyLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketTaxonomyLedgerUp.mk K S A R D H C P N => [K, S, A, R, D, H, C, P, N]

def socketTaxonomyLedgerToEventFlow :
    SocketTaxonomyLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (socketTaxonomyLedgerFields x).map socketTaxonomyLedgerEncodeBHist

def socketTaxonomyLedgerFromEventFlow :
    EventFlow → Option SocketTaxonomyLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _S :: [] => none
  | _K :: _S :: _A :: [] => none
  | _K :: _S :: _A :: _R :: [] => none
  | _K :: _S :: _A :: _R :: _D :: [] => none
  | _K :: _S :: _A :: _R :: _D :: _H :: [] => none
  | _K :: _S :: _A :: _R :: _D :: _H :: _C :: [] => none
  | _K :: _S :: _A :: _R :: _D :: _H :: _C :: _P :: [] => none
  | K :: S :: A :: R :: D :: H :: C :: P :: N :: [] =>
      some
        (SocketTaxonomyLedgerUp.mk
          (socketTaxonomyLedgerDecodeBHist K)
          (socketTaxonomyLedgerDecodeBHist S)
          (socketTaxonomyLedgerDecodeBHist A)
          (socketTaxonomyLedgerDecodeBHist R)
          (socketTaxonomyLedgerDecodeBHist D)
          (socketTaxonomyLedgerDecodeBHist H)
          (socketTaxonomyLedgerDecodeBHist C)
          (socketTaxonomyLedgerDecodeBHist P)
          (socketTaxonomyLedgerDecodeBHist N))
  | _K :: _S :: _A :: _R :: _D :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem socketTaxonomyLedger_round_trip :
    ∀ x : SocketTaxonomyLedgerUp,
      socketTaxonomyLedgerFromEventFlow (socketTaxonomyLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K S A R D H C P N =>
      exact
        congrArg some
          (socketTaxonomyLedger_mk_congr
            (socketTaxonomyLedgerDecode_encode_bhist K)
            (socketTaxonomyLedgerDecode_encode_bhist S)
            (socketTaxonomyLedgerDecode_encode_bhist A)
            (socketTaxonomyLedgerDecode_encode_bhist R)
            (socketTaxonomyLedgerDecode_encode_bhist D)
            (socketTaxonomyLedgerDecode_encode_bhist H)
            (socketTaxonomyLedgerDecode_encode_bhist C)
            (socketTaxonomyLedgerDecode_encode_bhist P)
            (socketTaxonomyLedgerDecode_encode_bhist N))

private theorem socketTaxonomyLedgerToEventFlow_injective
    {x y : SocketTaxonomyLedgerUp} :
    socketTaxonomyLedgerToEventFlow x = socketTaxonomyLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketTaxonomyLedgerFromEventFlow (socketTaxonomyLedgerToEventFlow x) =
        socketTaxonomyLedgerFromEventFlow (socketTaxonomyLedgerToEventFlow y) :=
    congrArg socketTaxonomyLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (socketTaxonomyLedger_round_trip x).symm
      (Eq.trans hread (socketTaxonomyLedger_round_trip y)))

private theorem socketTaxonomyLedger_field_faithful :
    ∀ x y : SocketTaxonomyLedgerUp,
      socketTaxonomyLedgerFields x = socketTaxonomyLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K S A R D H C P N =>
      cases y with
      | mk K' S' A' R' D' H' C' P' N' =>
          cases hfields
          rfl

instance socketTaxonomyLedgerBHistCarrier :
    BHistCarrier SocketTaxonomyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketTaxonomyLedgerToEventFlow
  fromEventFlow := socketTaxonomyLedgerFromEventFlow

instance socketTaxonomyLedgerChapterTasteGate :
    ChapterTasteGate SocketTaxonomyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketTaxonomyLedgerFromEventFlow (socketTaxonomyLedgerToEventFlow x) = some x
    exact socketTaxonomyLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (socketTaxonomyLedgerToEventFlow_injective heq)

instance socketTaxonomyLedgerFieldFaithful :
    FieldFaithful SocketTaxonomyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketTaxonomyLedgerFields
  field_faithful := socketTaxonomyLedger_field_faithful

instance socketTaxonomyLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SocketTaxonomyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketTaxonomyLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SocketTaxonomyLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SocketTaxonomyLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  socketTaxonomyLedgerChapterTasteGate

theorem SocketTaxonomyLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, socketTaxonomyLedgerDecodeBHist (socketTaxonomyLedgerEncodeBHist h) = h) ∧
      (∀ x : SocketTaxonomyLedgerUp,
        socketTaxonomyLedgerFromEventFlow (socketTaxonomyLedgerToEventFlow x) = some x) ∧
        (∀ x y : SocketTaxonomyLedgerUp,
          socketTaxonomyLedgerToEventFlow x = socketTaxonomyLedgerToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful SocketTaxonomyLedgerUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨socketTaxonomyLedgerDecode_encode_bhist,
      socketTaxonomyLedger_round_trip,
      (fun _ _ heq => socketTaxonomyLedgerToEventFlow_injective heq),
      ⟨socketTaxonomyLedgerFieldFaithful⟩⟩

end BEDC.Derived.SocketTaxonomyLedgerUp
