import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubtractionUp

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

inductive RegularCauchySubtractionUp : Type where
  | mk (X Y G A W D E S H C P N : BHist) : RegularCauchySubtractionUp
  deriving DecidableEq

def RegularCauchySubtractionCarrier [AskSetup] [PackageSetup]
    (X Y G A W D E S H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory G ∧ UnaryHistory A ∧
    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory S ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

def regularCauchySubtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubtractionEncodeBHist h

def regularCauchySubtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubtractionDecodeBHist tail)

private theorem regularCauchySubtraction_decode_encode :
    ∀ h : BHist,
      regularCauchySubtractionDecodeBHist
          (regularCauchySubtractionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubtractionFields :
    RegularCauchySubtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubtractionUp.mk X Y G A W D E S H C P N =>
      [X, Y, G, A, W, D, E, S, H, C, P, N]

def regularCauchySubtractionToEventFlow :
    RegularCauchySubtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchySubtractionEncodeBHist
        (regularCauchySubtractionFields x)

private def regularCauchySubtractionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySubtractionRawAt index rest

def regularCauchySubtractionFromEventFlow
    (flow : EventFlow) : Option RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySubtractionUp.mk
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 0 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 1 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 2 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 3 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 4 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 5 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 6 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 7 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 8 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 9 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 10 flow))
      (regularCauchySubtractionDecodeBHist (regularCauchySubtractionRawAt 11 flow)))

private theorem regularCauchySubtraction_round_trip :
    ∀ x : RegularCauchySubtractionUp,
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G A W D E S H C P N =>
      change
        some
          (RegularCauchySubtractionUp.mk
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist X))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist Y))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist G))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist A))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist W))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist D))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist E))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist S))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist H))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist C))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist P))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist N))) =
          some (RegularCauchySubtractionUp.mk X Y G A W D E S H C P N)
      rw [regularCauchySubtraction_decode_encode X,
        regularCauchySubtraction_decode_encode Y,
        regularCauchySubtraction_decode_encode G,
        regularCauchySubtraction_decode_encode A,
        regularCauchySubtraction_decode_encode W,
        regularCauchySubtraction_decode_encode D,
        regularCauchySubtraction_decode_encode E,
        regularCauchySubtraction_decode_encode S,
        regularCauchySubtraction_decode_encode H,
        regularCauchySubtraction_decode_encode C,
        regularCauchySubtraction_decode_encode P,
        regularCauchySubtraction_decode_encode N]

private theorem regularCauchySubtractionToEventFlow_injective
    {x y : RegularCauchySubtractionUp} :
    regularCauchySubtractionToEventFlow x =
        regularCauchySubtractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow y) :=
    congrArg regularCauchySubtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubtraction_round_trip x).symm
      (Eq.trans hread (regularCauchySubtraction_round_trip y)))

instance regularCauchySubtractionBHistCarrier :
    BHistCarrier RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubtractionToEventFlow
  fromEventFlow := regularCauchySubtractionFromEventFlow

instance regularCauchySubtractionChapterTasteGate :
    ChapterTasteGate RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        some x
    exact regularCauchySubtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubtractionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubtractionChapterTasteGate

theorem RegularCauchySubtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySubtractionDecodeBHist
          (regularCauchySubtractionEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchySubtractionUp,
        regularCauchySubtractionFromEventFlow
            (regularCauchySubtractionToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchySubtractionUp,
          regularCauchySubtractionToEventFlow x =
              regularCauchySubtractionToEventFlow y →
            x = y) ∧
          regularCauchySubtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySubtraction_decode_encode,
      regularCauchySubtraction_round_trip,
      by
        intro x y heq
        exact regularCauchySubtractionToEventFlow_injective heq,
      rfl⟩

theorem RegularCauchySubtractionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y G A W D E S H C P N read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubtractionCarrier X Y G A W D E S H C P N bundle pkg ->
      Cont H C read ->
        PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row Y ∨ hsame row G ∨ hsame row A ∨
                  hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row S ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont H C read ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier replay localPkg
  obtain ⟨_xUnary, _yUnary, _gUnary, _aUnary, _wUnary, _dUnary, _eUnary, _sUnary,
    hUnary, cUnary, _pUnary, nUnary, _provenancePkg, _carrierNamePkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed hUnary cUnary replay
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row G ∨ hsame row A ∨
              hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row S ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H C read ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replay, localPkg⟩
  }
  exact ⟨cert, readUnary⟩

end BEDC.Derived.RegularCauchySubtractionUp
