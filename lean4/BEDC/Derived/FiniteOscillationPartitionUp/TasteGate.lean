import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOscillationPartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOscillationPartitionUp : Type where
  | mk (I M A B R H C P N : BHist) : FiniteOscillationPartitionUp
  deriving DecidableEq

def finiteOscillationPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOscillationPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOscillationPartitionEncodeBHist h

def finiteOscillationPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOscillationPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOscillationPartitionDecodeBHist tail)

private theorem finiteOscillationPartition_decode_encode :
    ∀ h : BHist, finiteOscillationPartitionDecodeBHist
      (finiteOscillationPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteOscillationPartitionFields : FiniteOscillationPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationPartitionUp.mk I M A B R H C P N =>
      [I, M, A, B, R, H, C, P, N]

def finiteOscillationPartitionToEventFlow : FiniteOscillationPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteOscillationPartitionFields x).map finiteOscillationPartitionEncodeBHist

private def finiteOscillationPartitionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteOscillationPartitionRawAt n rest

private def finiteOscillationPartitionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteOscillationPartitionLengthEq n rest

def finiteOscillationPartitionFromEventFlow : EventFlow → Option FiniteOscillationPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteOscillationPartitionLengthEq 9 flow with
      | true =>
          some
            (FiniteOscillationPartitionUp.mk
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 0 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 1 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 2 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 3 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 4 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 5 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 6 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 7 flow))
              (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionRawAt 8 flow)))
      | false => none

private theorem finiteOscillationPartition_round_trip :
    ∀ x : FiniteOscillationPartitionUp,
      finiteOscillationPartitionFromEventFlow
        (finiteOscillationPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M A B R H C P N =>
      change
        some
          (FiniteOscillationPartitionUp.mk
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist I))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist M))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist A))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist B))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist R))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist H))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist C))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist P))
            (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEncodeBHist N))) =
          some (FiniteOscillationPartitionUp.mk I M A B R H C P N)
      rw [finiteOscillationPartition_decode_encode I,
        finiteOscillationPartition_decode_encode M,
        finiteOscillationPartition_decode_encode A,
        finiteOscillationPartition_decode_encode B,
        finiteOscillationPartition_decode_encode R,
        finiteOscillationPartition_decode_encode H,
        finiteOscillationPartition_decode_encode C,
        finiteOscillationPartition_decode_encode P,
        finiteOscillationPartition_decode_encode N]

private theorem finiteOscillationPartitionToEventFlow_injective
    {x y : FiniteOscillationPartitionUp} :
    finiteOscillationPartitionToEventFlow x =
      finiteOscillationPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOscillationPartitionFromEventFlow (finiteOscillationPartitionToEventFlow x) =
        finiteOscillationPartitionFromEventFlow (finiteOscillationPartitionToEventFlow y) :=
    congrArg finiteOscillationPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOscillationPartition_round_trip x).symm
      (Eq.trans hread (finiteOscillationPartition_round_trip y)))

private theorem finiteOscillationPartition_fields_faithful :
    ∀ x y : FiniteOscillationPartitionUp, finiteOscillationPartitionFields x =
      finiteOscillationPartitionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 M1 A1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 A2 B2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteOscillationPartitionBHistCarrier :
    BHistCarrier FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOscillationPartitionToEventFlow
  fromEventFlow := finiteOscillationPartitionFromEventFlow

instance finiteOscillationPartitionChapterTasteGate :
    ChapterTasteGate FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOscillationPartitionFromEventFlow
        (finiteOscillationPartitionToEventFlow x) = some x
    exact finiteOscillationPartition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOscillationPartitionToEventFlow_injective heq)

instance finiteOscillationPartitionFieldFaithful :
    FieldFaithful FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteOscillationPartitionFields
  field_faithful := finiteOscillationPartition_fields_faithful

instance finiteOscillationPartitionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteOscillationPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteOscillationPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteOscillationPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOscillationPartitionChapterTasteGate

structure FiniteOscillationPartitionCarrier [AskSetup] [PackageSetup]
    (I M A B R H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop where
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  unaryI : UnaryHistory I
  unaryM : UnaryHistory M
  unaryA : UnaryHistory A
  unaryB : UnaryHistory B
  unaryR : UnaryHistory R
  unaryH : UnaryHistory H
  unaryC : UnaryHistory C
  unaryP : UnaryHistory P
  unaryN : UnaryHistory N
  contIMA : Cont I M A
  contABR : Cont A B R
  contRHC : Cont R H C
  pkgP : PkgSig bundle P pkg
  pkgN : PkgSig bundle N pkg

theorem FiniteOscillationPartition_namecert_obligations [AskSetup] [PackageSetup]
    {I M A B R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteOscillationPartitionCarrier I M A B R H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FiniteOscillationPartitionCarrier I M A B R H C P N bundle pkg ∧
            (hsame row I ∨ hsame row M ∨ hsame row A ∨ hsame row B ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N))
        (fun _row : BHist =>
          Cont I M A ∧ Cont A B R ∧ Cont R H C ∧ PkgSig bundle P pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N (And.intro carrier (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (hsame_refl N))))))))))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left.contIMA, source.left.contABR, source.left.contRHC,
        source.left.pkgP⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl hrow =>
          cases hrow
          exact ⟨source.left.unaryI, carrier.pkgN⟩
      | inr rest =>
          cases rest with
          | inl hrow =>
              cases hrow
              exact ⟨source.left.unaryM, carrier.pkgN⟩
          | inr rest =>
              cases rest with
              | inl hrow =>
                  cases hrow
                  exact ⟨source.left.unaryA, carrier.pkgN⟩
              | inr rest =>
                  cases rest with
                  | inl hrow =>
                      cases hrow
                      exact ⟨source.left.unaryB, carrier.pkgN⟩
                  | inr rest =>
                      cases rest with
                      | inl hrow =>
                          cases hrow
                          exact ⟨source.left.unaryR, carrier.pkgN⟩
                      | inr rest =>
                          cases rest with
                          | inl hrow =>
                              cases hrow
                              exact ⟨source.left.unaryH, carrier.pkgN⟩
                          | inr rest =>
                              cases rest with
                              | inl hrow =>
                                  cases hrow
                                  exact ⟨source.left.unaryC, carrier.pkgN⟩
                              | inr rest =>
                                  cases rest with
                                  | inl hrow =>
                                      cases hrow
                                      exact ⟨source.left.unaryP, carrier.pkgN⟩
                                  | inr hrow =>
                                      cases hrow
                                      exact ⟨source.left.unaryN, carrier.pkgN⟩
  }

end BEDC.Derived.FiniteOscillationPartitionUp
