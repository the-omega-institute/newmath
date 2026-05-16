import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompressionLedgerFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompressionLedgerFunctorUp : Type where
  | mk (A K E R O M L Q J H C P N : BHist) : CompressionLedgerFunctorUp
  deriving DecidableEq

def compressionLedgerFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compressionLedgerFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compressionLedgerFunctorEncodeBHist h

def compressionLedgerFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compressionLedgerFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compressionLedgerFunctorDecodeBHist tail)

private theorem compressionLedgerFunctorDecodeEncodeBHist :
    ∀ h : BHist,
      compressionLedgerFunctorDecodeBHist
        (compressionLedgerFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compressionLedgerFunctorFields : CompressionLedgerFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N =>
      [A, K, E, R, O, M, L, Q, J, H, C, P, N]

def compressionLedgerFunctorToEventFlow : CompressionLedgerFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compressionLedgerFunctorFields x).map compressionLedgerFunctorEncodeBHist

def compressionLedgerFunctorFromEventFlow :
    EventFlow → Option CompressionLedgerFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: K :: E :: R :: O :: M :: L :: Q :: J :: H :: C :: P :: N :: [] =>
      some
        (CompressionLedgerFunctorUp.mk
          (compressionLedgerFunctorDecodeBHist A)
          (compressionLedgerFunctorDecodeBHist K)
          (compressionLedgerFunctorDecodeBHist E)
          (compressionLedgerFunctorDecodeBHist R)
          (compressionLedgerFunctorDecodeBHist O)
          (compressionLedgerFunctorDecodeBHist M)
          (compressionLedgerFunctorDecodeBHist L)
          (compressionLedgerFunctorDecodeBHist Q)
          (compressionLedgerFunctorDecodeBHist J)
          (compressionLedgerFunctorDecodeBHist H)
          (compressionLedgerFunctorDecodeBHist C)
          (compressionLedgerFunctorDecodeBHist P)
          (compressionLedgerFunctorDecodeBHist N))
  | _ => none

private theorem compressionLedgerFunctor_round_trip :
    ∀ x : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFromEventFlow
        (compressionLedgerFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A K E R O M L Q J H C P N =>
      change
        some
          (CompressionLedgerFunctorUp.mk
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist A))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist K))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist E))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist R))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist O))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist M))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist L))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist Q))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist J))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist H))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist C))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist P))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist N))) =
          some (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N)
      rw [compressionLedgerFunctorDecodeEncodeBHist A,
        compressionLedgerFunctorDecodeEncodeBHist K,
        compressionLedgerFunctorDecodeEncodeBHist E,
        compressionLedgerFunctorDecodeEncodeBHist R,
        compressionLedgerFunctorDecodeEncodeBHist O,
        compressionLedgerFunctorDecodeEncodeBHist M,
        compressionLedgerFunctorDecodeEncodeBHist L,
        compressionLedgerFunctorDecodeEncodeBHist Q,
        compressionLedgerFunctorDecodeEncodeBHist J,
        compressionLedgerFunctorDecodeEncodeBHist H,
        compressionLedgerFunctorDecodeEncodeBHist C,
        compressionLedgerFunctorDecodeEncodeBHist P,
        compressionLedgerFunctorDecodeEncodeBHist N]

private theorem compressionLedgerFunctorToEventFlow_injective
    {x y : CompressionLedgerFunctorUp} :
    compressionLedgerFunctorToEventFlow x =
      compressionLedgerFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) =
        compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow y) :=
    congrArg compressionLedgerFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compressionLedgerFunctor_round_trip x).symm
      (Eq.trans hread (compressionLedgerFunctor_round_trip y)))

private theorem compressionLedgerFunctor_fields_faithful :
    ∀ x y : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFields x = compressionLedgerFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ K₁ E₁ R₁ O₁ M₁ L₁ Q₁ J₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ K₂ E₂ R₂ O₂ M₂ L₂ Q₂ J₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA t0
          injection t0 with hK t1
          injection t1 with hE t2
          injection t2 with hR t3
          injection t3 with hO t4
          injection t4 with hM t5
          injection t5 with hL t6
          injection t6 with hQ t7
          injection t7 with hJ t8
          injection t8 with hH t9
          injection t9 with hC t10
          injection t10 with hP t11
          injection t11 with hN _
          subst hA
          subst hK
          subst hE
          subst hR
          subst hO
          subst hM
          subst hL
          subst hQ
          subst hJ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance compressionLedgerFunctorBHistCarrier :
    BHistCarrier CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compressionLedgerFunctorToEventFlow
  fromEventFlow := compressionLedgerFunctorFromEventFlow

instance compressionLedgerFunctorChapterTasteGate :
    ChapterTasteGate CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compressionLedgerFunctorFromEventFlow
        (compressionLedgerFunctorToEventFlow x) = some x
    exact compressionLedgerFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compressionLedgerFunctorToEventFlow_injective heq)

instance compressionLedgerFunctorFieldFaithful :
    FieldFaithful CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compressionLedgerFunctorFields
  field_faithful := compressionLedgerFunctor_fields_faithful

instance compressionLedgerFunctorNontrivial :
    Nontrivial CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompressionLedgerFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compressionLedgerFunctorChapterTasteGate

end BEDC.Derived.CompressionLedgerFunctorUp
