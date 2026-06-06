import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArithmeticProgressionUp

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

inductive RealArithmeticProgressionUp : Type where
  | mk (a d S R D H C P N : BHist) : RealArithmeticProgressionUp
  deriving DecidableEq

def realArithmeticProgressionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArithmeticProgressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArithmeticProgressionEncodeBHist h

def realArithmeticProgressionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArithmeticProgressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArithmeticProgressionDecodeBHist tail)

private theorem realArithmeticProgression_decode_encode_bhist :
    ∀ h : BHist,
      realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realArithmeticProgressionFields :
    RealArithmeticProgressionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArithmeticProgressionUp.mk a d S R D H C P N => [a, d, S, R, D, H, C, P, N]

def realArithmeticProgressionToEventFlow :
    RealArithmeticProgressionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realArithmeticProgressionFields x).map realArithmeticProgressionEncodeBHist

private def realArithmeticProgressionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realArithmeticProgressionEventAtDefault index rest

def realArithmeticProgressionFromEventFlow :
    EventFlow -> Option RealArithmeticProgressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealArithmeticProgressionUp.mk
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 0 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 1 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 2 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 3 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 4 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 5 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 6 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 7 ef))
        (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 8 ef)))

private theorem realArithmeticProgression_round_trip :
    ∀ x : RealArithmeticProgressionUp,
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a d S R D H C P N =>
      change
        some
          (RealArithmeticProgressionUp.mk
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist a))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist d))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist S))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist R))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist D))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist H))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist C))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist P))
            (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist N))) =
          some (RealArithmeticProgressionUp.mk a d S R D H C P N)
      rw [realArithmeticProgression_decode_encode_bhist a,
        realArithmeticProgression_decode_encode_bhist d,
        realArithmeticProgression_decode_encode_bhist S,
        realArithmeticProgression_decode_encode_bhist R,
        realArithmeticProgression_decode_encode_bhist D,
        realArithmeticProgression_decode_encode_bhist H,
        realArithmeticProgression_decode_encode_bhist C,
        realArithmeticProgression_decode_encode_bhist P,
        realArithmeticProgression_decode_encode_bhist N]

private theorem realArithmeticProgressionToEventFlow_injective
    {x y : RealArithmeticProgressionUp} :
    realArithmeticProgressionToEventFlow x = realArithmeticProgressionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
        realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow y) :=
    congrArg realArithmeticProgressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realArithmeticProgression_round_trip x).symm
      (Eq.trans hread (realArithmeticProgression_round_trip y)))

instance realArithmeticProgressionBHistCarrier :
    BHistCarrier RealArithmeticProgressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArithmeticProgressionToEventFlow
  fromEventFlow := realArithmeticProgressionFromEventFlow

instance realArithmeticProgressionChapterTasteGate :
    ChapterTasteGate RealArithmeticProgressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
        some x
    exact realArithmeticProgression_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realArithmeticProgressionToEventFlow_injective heq)

instance realArithmeticProgressionNontrivial :
    Nontrivial RealArithmeticProgressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealArithmeticProgressionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealArithmeticProgressionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealArithmeticProgressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realArithmeticProgressionChapterTasteGate

theorem RealArithmeticProgressionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist h) = h) ∧
      (∀ x : RealArithmeticProgressionUp,
        realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
          some x) ∧
        (∀ x y : RealArithmeticProgressionUp,
          realArithmeticProgressionToEventFlow x = realArithmeticProgressionToEventFlow y →
            x = y) ∧
          realArithmeticProgressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realArithmeticProgression_decode_encode_bhist, realArithmeticProgression_round_trip,
      fun _x _y heq => realArithmeticProgressionToEventFlow_injective heq, rfl⟩

def RealArithmeticProgressionCarrier [AskSetup] [PackageSetup]
    (a d S R D H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory a ∧ UnaryHistory d ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont S D R ∧ Cont R C H ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RealArithmeticProgressionNameCertObligations [AskSetup] [PackageSetup]
    {a d S R D H C P N scheduleRead dyadicRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealArithmeticProgressionCarrier a d S R D H C P N bundle pkg ->
      Cont S D dyadicRead ->
        Cont dyadicRead R regularRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row a ∨ hsame row d ∨ hsame row S ∨ hsame row R ∨
                      hsame row D ∨ hsame row regularRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S D dyadicRead ∧
                      Cont dyadicRead R regularRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleDyadicRead dyadicRegularRead provenancePkg namePkg
  obtain ⟨_aUnary, _dUnary, sUnary, rUnary, dUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierDyadic, _carrierHandoff, _carrierProvenance, _carrierName⟩ :=
      carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sUnary dUnary scheduleDyadicRead
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary dyadicRegularRead
  have sourceRegular :
      (fun row : BHist => hsame row regularRead ∧ UnaryHistory row) regularRead := by
    exact ⟨hsame_refl regularRead, regularUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row a ∨ hsame row d ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S D dyadicRead ∧ Cont dyadicRead R regularRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead sourceRegular
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleDyadicRead, dyadicRegularRead, provenancePkg, namePkg⟩
  }
  exact ⟨cert, regularUnary⟩

end BEDC.Derived.RealArithmeticProgressionUp
