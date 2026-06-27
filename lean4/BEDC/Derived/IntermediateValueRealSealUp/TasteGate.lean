import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntermediateValueRealSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntermediateValueRealSealUp : Type where
  | mk (I B A S W Q R H C P N : BHist) : IntermediateValueRealSealUp
  deriving DecidableEq

def intermediateValueRealSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intermediateValueRealSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intermediateValueRealSealEncodeBHist h

def intermediateValueRealSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intermediateValueRealSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intermediateValueRealSealDecodeBHist tail)

private theorem intermediateValueRealSealDecode_encode_bhist :
    ∀ h : BHist,
      intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def intermediateValueRealSealToEventFlow : IntermediateValueRealSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueRealSealUp.mk I B A S W Q R H C P N =>
      [[BMark.b0],
        intermediateValueRealSealEncodeBHist I,
        [BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        intermediateValueRealSealEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intermediateValueRealSealEncodeBHist N]

def intermediateValueRealSealFromEventFlow : EventFlow → Option IntermediateValueRealSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: I :: _tag1 :: B :: _tag2 :: A :: _tag3 :: S :: _tag4 :: W :: _tag5 ::
      Q :: _tag6 :: R :: _tag7 :: H :: _tag8 :: C :: _tag9 :: P :: _tag10 :: N ::
      [] =>
      some (IntermediateValueRealSealUp.mk
        (intermediateValueRealSealDecodeBHist I) (intermediateValueRealSealDecodeBHist B)
        (intermediateValueRealSealDecodeBHist A) (intermediateValueRealSealDecodeBHist S)
        (intermediateValueRealSealDecodeBHist W) (intermediateValueRealSealDecodeBHist Q)
        (intermediateValueRealSealDecodeBHist R) (intermediateValueRealSealDecodeBHist H)
        (intermediateValueRealSealDecodeBHist C) (intermediateValueRealSealDecodeBHist P)
        (intermediateValueRealSealDecodeBHist N))
  | _ => none

private theorem intermediateValueRealSeal_round_trip (x : IntermediateValueRealSealUp) :
    intermediateValueRealSealFromEventFlow (intermediateValueRealSealToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I B A S W Q R H C P N =>
      change
        some
          (IntermediateValueRealSealUp.mk
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist I))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist B))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist A))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist S))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist W))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist Q))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist R))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist H))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist C))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist P))
            (intermediateValueRealSealDecodeBHist (intermediateValueRealSealEncodeBHist N))) =
          some (IntermediateValueRealSealUp.mk I B A S W Q R H C P N)
      rw [intermediateValueRealSealDecode_encode_bhist I]
      rw [intermediateValueRealSealDecode_encode_bhist B]
      rw [intermediateValueRealSealDecode_encode_bhist A]
      rw [intermediateValueRealSealDecode_encode_bhist S]
      rw [intermediateValueRealSealDecode_encode_bhist W]
      rw [intermediateValueRealSealDecode_encode_bhist Q]
      rw [intermediateValueRealSealDecode_encode_bhist R]
      rw [intermediateValueRealSealDecode_encode_bhist H]
      rw [intermediateValueRealSealDecode_encode_bhist C]
      rw [intermediateValueRealSealDecode_encode_bhist P]
      rw [intermediateValueRealSealDecode_encode_bhist N]

private theorem intermediateValueRealSealToEventFlow_injective
    {x y : IntermediateValueRealSealUp} :
    intermediateValueRealSealToEventFlow x = intermediateValueRealSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intermediateValueRealSealFromEventFlow (intermediateValueRealSealToEventFlow x) =
        intermediateValueRealSealFromEventFlow (intermediateValueRealSealToEventFlow y) :=
    congrArg intermediateValueRealSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (intermediateValueRealSeal_round_trip x).symm
      (Eq.trans hread (intermediateValueRealSeal_round_trip y)))

def intermediateValueRealSealFields : IntermediateValueRealSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueRealSealUp.mk I B A S W Q R H C P N =>
      [I, B, A, S, W, Q, R, H, C, P, N]

private theorem intermediateValueRealSeal_field_faithful :
    ∀ x y : IntermediateValueRealSealUp,
      intermediateValueRealSealFields x = intermediateValueRealSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 B1 A1 S1 W1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 B2 A2 S2 W2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance intermediateValueRealSealBHistCarrier :
    BHistCarrier IntermediateValueRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intermediateValueRealSealToEventFlow
  fromEventFlow := intermediateValueRealSealFromEventFlow

instance intermediateValueRealSealChapterTasteGate :
    ChapterTasteGate IntermediateValueRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intermediateValueRealSealFromEventFlow (intermediateValueRealSealToEventFlow x) =
        some x
    exact intermediateValueRealSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intermediateValueRealSealToEventFlow_injective heq)

instance intermediateValueRealSealFieldFaithful :
    FieldFaithful IntermediateValueRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := intermediateValueRealSealFields
  field_faithful := intermediateValueRealSeal_field_faithful

instance intermediateValueRealSealNontrivial : Nontrivial IntermediateValueRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntermediateValueRealSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntermediateValueRealSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro heq
        cases heq⟩

def taste_gate : ChapterTasteGate IntermediateValueRealSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intermediateValueRealSealChapterTasteGate

theorem IntermediateValueRealSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I B A S W Q R H C P N leftRead rightRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I A leftRead ->
      Cont B S rightRead ->
        Cont leftRead rightRead sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row sealRead ∧
                  intermediateValueRealSealFields (IntermediateValueRealSealUp.mk I B A S W Q R H C P N) =
                    [I, B, A, S, W, Q, R, H, C, P, N])
              (fun row : BHist =>
                hsame row I ∨ hsame row B ∨ hsame row A ∨ hsame row S ∨ hsame row W ∨
                  hsame row Q ∨ hsame row R ∨ Cont I A leftRead ∨ Cont B S rightRead)
              (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
              hsame ∧
              intermediateValueRealSealFields (IntermediateValueRealSealUp.mk I B A S W Q R H C P N) =
                [I, B, A, S, W, Q, R, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro leftRoute _rightRoute _sealRoute pkgSig
  have fields_eq :
      intermediateValueRealSealFields (IntermediateValueRealSealUp.mk I B A S W Q R H C P N) =
        [I, B, A, S, W, Q, R, H, C, P, N] := by
    rfl
  have sourceSeal :
      (fun row : BHist =>
        hsame row sealRead ∧
          intermediateValueRealSealFields (IntermediateValueRealSealUp.mk I B A S W Q R H C P N) =
            [I, B, A, S, W, Q, R, H, C, P, N]) sealRead := by
    exact ⟨hsame_refl sealRead, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row sealRead ∧
            intermediateValueRealSealFields (IntermediateValueRealSealUp.mk I B A S W Q R H C P N) =
              [I, B, A, S, W, Q, R, H, C, P, N])
        (fun row : BHist =>
          hsame row I ∨ hsame row B ∨ hsame row A ∨ hsame row S ∨ hsame row W ∨
            hsame row Q ∨ hsame row R ∨ Cont I A leftRead ∨ Cont B S rightRead)
        (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl leftRoute)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, fields_eq⟩

end BEDC.Derived.IntermediateValueRealSealUp
