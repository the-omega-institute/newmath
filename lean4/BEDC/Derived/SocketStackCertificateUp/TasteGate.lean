import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketStackCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketStackCertificateUp : Type where
  | mk : (Q R E K A L H C P N : BHist) → SocketStackCertificateUp
  deriving DecidableEq

private def socketStackCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketStackCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketStackCertificateEncodeBHist h

private def socketStackCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketStackCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketStackCertificateDecodeBHist tail)

private theorem socketStackCertificate_decode_encode_bhist :
    ∀ h : BHist,
      socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def socketStackCertificateFields : SocketStackCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketStackCertificateUp.mk Q R E K A L H C P N =>
      [Q, R, E, K, A, L, H, C, P, N]

private def socketStackCertificateToEventFlow : SocketStackCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (socketStackCertificateFields x).map socketStackCertificateEncodeBHist

private def socketStackCertificateFromEventFlow :
    EventFlow → Option SocketStackCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: R :: E :: K :: A :: L :: H :: C :: P :: N :: [] =>
      some
        (SocketStackCertificateUp.mk
          (socketStackCertificateDecodeBHist Q)
          (socketStackCertificateDecodeBHist R)
          (socketStackCertificateDecodeBHist E)
          (socketStackCertificateDecodeBHist K)
          (socketStackCertificateDecodeBHist A)
          (socketStackCertificateDecodeBHist L)
          (socketStackCertificateDecodeBHist H)
          (socketStackCertificateDecodeBHist C)
          (socketStackCertificateDecodeBHist P)
          (socketStackCertificateDecodeBHist N))
  | _ => none

private theorem socketStackCertificate_round_trip :
    ∀ x : SocketStackCertificateUp,
      socketStackCertificateFromEventFlow (socketStackCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q R E K A L H C P N =>
      change
        some
          (SocketStackCertificateUp.mk
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist Q))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist R))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist E))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist K))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist A))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist L))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist H))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist C))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist P))
            (socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist N))) =
          some (SocketStackCertificateUp.mk Q R E K A L H C P N)
      rw [socketStackCertificate_decode_encode_bhist Q,
        socketStackCertificate_decode_encode_bhist R,
        socketStackCertificate_decode_encode_bhist E,
        socketStackCertificate_decode_encode_bhist K,
        socketStackCertificate_decode_encode_bhist A,
        socketStackCertificate_decode_encode_bhist L,
        socketStackCertificate_decode_encode_bhist H,
        socketStackCertificate_decode_encode_bhist C,
        socketStackCertificate_decode_encode_bhist P,
        socketStackCertificate_decode_encode_bhist N]

private theorem socketStackCertificateToEventFlow_injective
    {x y : SocketStackCertificateUp} :
    socketStackCertificateToEventFlow x = socketStackCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketStackCertificateFromEventFlow (socketStackCertificateToEventFlow x) =
        socketStackCertificateFromEventFlow (socketStackCertificateToEventFlow y) :=
    congrArg socketStackCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (socketStackCertificate_round_trip x).symm
      (Eq.trans hread (socketStackCertificate_round_trip y)))

private theorem socketStackCertificate_fields_faithful :
    ∀ x y : SocketStackCertificateUp,
      socketStackCertificateFields x = socketStackCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ R₁ E₁ K₁ A₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ R₂ E₂ K₂ A₂ L₂ H₂ C₂ P₂ N₂ =>
          change
              [Q₁, R₁, E₁, K₁, A₁, L₁, H₁, C₁, P₁, N₁] =
                [Q₂, R₂, E₂, K₂, A₂, L₂, H₂, C₂, P₂, N₂] at hfields
          injection hfields with hQ t1
          injection t1 with hR t2
          injection t2 with hE t3
          injection t3 with hK t4
          injection t4 with hA t5
          injection t5 with hL t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hQ
          cases hR
          cases hE
          cases hK
          cases hA
          cases hL
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance socketStackCertificateBHistCarrier :
    BHistCarrier SocketStackCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketStackCertificateToEventFlow
  fromEventFlow := socketStackCertificateFromEventFlow

instance socketStackCertificateChapterTasteGate :
    ChapterTasteGate SocketStackCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketStackCertificateFromEventFlow (socketStackCertificateToEventFlow x) = some x
    exact socketStackCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (socketStackCertificateToEventFlow_injective heq)

instance socketStackCertificateFieldFaithful :
    FieldFaithful SocketStackCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketStackCertificateFields
  field_faithful := socketStackCertificate_fields_faithful

instance socketStackCertificateNontrivial :
    Nontrivial SocketStackCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketStackCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SocketStackCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SocketStackCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  socketStackCertificateChapterTasteGate

theorem SocketStackCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      socketStackCertificateDecodeBHist (socketStackCertificateEncodeBHist h) = h) ∧
      (∀ Q R E K A L H C P N : BHist,
        socketStackCertificateFields
            (SocketStackCertificateUp.mk Q R E K A L H C P N) =
          [Q, R, E, K, A, L, H, C, P, N]) ∧
        socketStackCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact socketStackCertificate_decode_encode_bhist
  · constructor
    · intro Q R E K A L H C P N
      rfl
    · rfl

end BEDC.Derived.SocketStackCertificateUp
