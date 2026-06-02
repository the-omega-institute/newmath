import BEDC.Derived.AbelRuffiniUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelRuffiniUp

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

inductive AbelRuffiniUp : Type where
  | mk
      (polynomial baseField galoisRow symRow derivedLedger transport route provenance
        localName consumerRead : BHist) :
      AbelRuffiniUp
  deriving DecidableEq

private def abelRuffiniEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelRuffiniEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelRuffiniEncodeBHist h

private def abelRuffiniDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelRuffiniDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelRuffiniDecodeBHist tail)

private theorem abelRuffini_decode_encode_bhist :
    ∀ h : BHist, abelRuffiniDecodeBHist (abelRuffiniEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def abelRuffiniFields : AbelRuffiniUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelRuffiniUp.mk polynomial baseField galoisRow symRow derivedLedger transport route
      provenance localName consumerRead =>
      [polynomial, baseField, galoisRow, symRow, derivedLedger, transport, route,
        provenance, localName, consumerRead]

private def abelRuffiniToEventFlow : AbelRuffiniUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abelRuffiniFields x).map abelRuffiniEncodeBHist

private def abelRuffiniEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelRuffiniEventAtDefault index rest

private def abelRuffiniFromEventFlow (ef : EventFlow) : Option AbelRuffiniUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelRuffiniUp.mk
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 0 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 1 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 2 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 3 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 4 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 5 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 6 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 7 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 8 ef))
      (abelRuffiniDecodeBHist (abelRuffiniEventAtDefault 9 ef)))

private theorem abelRuffini_round_trip :
    ∀ x : AbelRuffiniUp,
      abelRuffiniFromEventFlow (abelRuffiniToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk polynomial baseField galoisRow symRow derivedLedger transport route provenance
      localName consumerRead =>
      change
        some
          (AbelRuffiniUp.mk
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist polynomial))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist baseField))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist galoisRow))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist symRow))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist derivedLedger))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist transport))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist route))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist provenance))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist localName))
            (abelRuffiniDecodeBHist (abelRuffiniEncodeBHist consumerRead))) =
          some
            (AbelRuffiniUp.mk polynomial baseField galoisRow symRow derivedLedger
              transport route provenance localName consumerRead)
      rw [abelRuffini_decode_encode_bhist polynomial,
        abelRuffini_decode_encode_bhist baseField,
        abelRuffini_decode_encode_bhist galoisRow,
        abelRuffini_decode_encode_bhist symRow,
        abelRuffini_decode_encode_bhist derivedLedger,
        abelRuffini_decode_encode_bhist transport,
        abelRuffini_decode_encode_bhist route,
        abelRuffini_decode_encode_bhist provenance,
        abelRuffini_decode_encode_bhist localName,
        abelRuffini_decode_encode_bhist consumerRead]

private theorem abelRuffiniToEventFlow_injective {x y : AbelRuffiniUp} :
    abelRuffiniToEventFlow x = abelRuffiniToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelRuffiniFromEventFlow (abelRuffiniToEventFlow x) =
        abelRuffiniFromEventFlow (abelRuffiniToEventFlow y) :=
    congrArg abelRuffiniFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (abelRuffini_round_trip x).symm
      (Eq.trans hread (abelRuffini_round_trip y)))

instance abelRuffiniBHistCarrier : BHistCarrier AbelRuffiniUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelRuffiniToEventFlow
  fromEventFlow := abelRuffiniFromEventFlow

instance abelRuffiniChapterTasteGate : ChapterTasteGate AbelRuffiniUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelRuffiniFromEventFlow (abelRuffiniToEventFlow x) = some x
    exact abelRuffini_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (abelRuffiniToEventFlow_injective heq)

instance abelRuffiniNontrivial : Nontrivial AbelRuffiniUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelRuffiniUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbelRuffiniUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AbelRuffiniDegreeFiveConsumerExamples [AskSetup] [PackageSetup]
    {polynomial baseField galoisRow symRow derivedLedger transport route provenance localName
      consumerRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory polynomial ->
      UnaryHistory baseField ->
        UnaryHistory galoisRow ->
          UnaryHistory symRow ->
            UnaryHistory derivedLedger ->
              UnaryHistory transport ->
                UnaryHistory route ->
                  UnaryHistory provenance ->
                    UnaryHistory localName ->
                      Cont polynomial baseField galoisRow ->
                        Cont galoisRow symRow derivedLedger ->
                          Cont derivedLedger transport route ->
                            Cont route provenance consumerRead ->
                              PkgSig bundle localName pkg ->
                                Nonempty (ChapterTasteGate AbelRuffiniUp) ∧
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row consumerRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row polynomial ∨ hsame row baseField ∨
                                          hsame row galoisRow ∨ hsame row symRow ∨
                                            hsame row derivedLedger ∨ hsame row route ∨
                                              hsame row consumerRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert
  intro polynomialUnary baseUnary _galoisUnary symUnary _derivedUnary transportUnary
    _routeUnary provenanceUnary _localNameUnary polynomialRoute galoisRoute
    derivedRoute consumerRoute localNamePkg
  have galoisClosed : UnaryHistory galoisRow :=
    unary_cont_closed polynomialUnary baseUnary polynomialRoute
  have derivedClosed : UnaryHistory derivedLedger :=
    unary_cont_closed galoisClosed symUnary galoisRoute
  have routeClosed : UnaryHistory route :=
    unary_cont_closed derivedClosed transportUnary derivedRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed routeClosed provenanceUnary consumerRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) hsame := {
    carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
      intro _row _other sameRows sourceRow
      exact
        ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
          unary_transport sourceRow.right sameRows⟩
  }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row polynomial ∨ hsame row baseField ∨ hsame row galoisRow ∨
              hsame row symRow ∨ hsame row derivedLedger ∨ hsame row route ∨
                hsame row consumerRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := {
    core := core
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, localNamePkg⟩
  }
  exact ⟨⟨abelRuffiniChapterTasteGate⟩, cert, consumerUnary⟩

end BEDC.Derived.AbelRuffiniUp
