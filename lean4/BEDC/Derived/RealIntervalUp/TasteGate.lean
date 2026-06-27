import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalUp : Type where
  | mk (L U E D W R S H C P N : BHist) : RealIntervalUp

def realIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalEncodeBHist h

def realIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalDecodeBHist tail)

private theorem RealIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realIntervalDecodeBHist (realIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalFields : RealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalUp.mk L U E D W R S H C P N => [L, U, E, D, W, R, S, H, C, P, N]

def realIntervalToEventFlow : RealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realIntervalFields x).map realIntervalEncodeBHist

private def realIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalEventAtDefault index rest

def realIntervalFromEventFlow (ef : EventFlow) : Option RealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalUp.mk
      (realIntervalDecodeBHist (realIntervalEventAtDefault 0 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 1 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 2 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 3 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 4 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 5 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 6 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 7 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 8 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 9 ef))
      (realIntervalDecodeBHist (realIntervalEventAtDefault 10 ef)))

private theorem RealIntervalTasteGate_single_carrier_alignment_round_trip
    (x : RealIntervalUp) :
    realIntervalFromEventFlow (realIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U E D W R S H C P N =>
      change
        some
          (RealIntervalUp.mk
            (realIntervalDecodeBHist (realIntervalEncodeBHist L))
            (realIntervalDecodeBHist (realIntervalEncodeBHist U))
            (realIntervalDecodeBHist (realIntervalEncodeBHist E))
            (realIntervalDecodeBHist (realIntervalEncodeBHist D))
            (realIntervalDecodeBHist (realIntervalEncodeBHist W))
            (realIntervalDecodeBHist (realIntervalEncodeBHist R))
            (realIntervalDecodeBHist (realIntervalEncodeBHist S))
            (realIntervalDecodeBHist (realIntervalEncodeBHist H))
            (realIntervalDecodeBHist (realIntervalEncodeBHist C))
            (realIntervalDecodeBHist (realIntervalEncodeBHist P))
            (realIntervalDecodeBHist (realIntervalEncodeBHist N))) =
          some (RealIntervalUp.mk L U E D W R S H C P N)
      rw [RealIntervalTasteGate_single_carrier_alignment_decode_encode L,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode U,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode E,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode D,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode W,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode R,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode S,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode H,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode C,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode P,
        RealIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealIntervalTasteGate_single_carrier_alignment_injective
    {x y : RealIntervalUp} :
    realIntervalToEventFlow x = realIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalFromEventFlow (realIntervalToEventFlow x) =
        realIntervalFromEventFlow (realIntervalToEventFlow y) :=
    congrArg realIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance realIntervalBHistCarrier : BHistCarrier RealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalToEventFlow
  fromEventFlow := realIntervalFromEventFlow

instance realIntervalChapterTasteGate : ChapterTasteGate RealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalFromEventFlow (realIntervalToEventFlow x) = some x
    exact RealIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntervalTasteGate_single_carrier_alignment_injective heq)

theorem RealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, realIntervalDecodeBHist (realIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealIntervalUp) ∧
        Nonempty (ChapterTasteGate RealIntervalUp) ∧
          realIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealIntervalTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨realIntervalBHistCarrier⟩
    · constructor
      · exact ⟨realIntervalChapterTasteGate⟩
      · rfl

theorem RealIntervalCarrier_namecert_obligations (L U E D W R S H C P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
            hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N)
        (fun row : BHist =>
          hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
            hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N)
        (fun row : BHist =>
          hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
            hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N)
        hsame ∧
      realIntervalFields (RealIntervalUp.mk L U E D W R S H C P N) =
        [L, U, E, D, W, R, S, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  let carrier := fun row : BHist =>
    hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
      hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
        hsame row N
  have cert : SemanticNameCert carrier carrier carrier hsame := {
    core := {
      carrier_inhabited := Exists.intro L (Or.inl (hsame_refl L))
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        cases source with
        | inl sameL =>
            exact Or.inl (lift sameL)
        | inr tail1 =>
            cases tail1 with
            | inl sameU =>
                exact Or.inr (Or.inl (lift sameU))
            | inr tail2 =>
                cases tail2 with
                | inl sameE =>
                    exact Or.inr (Or.inr (Or.inl (lift sameE)))
                | inr tail3 =>
                    cases tail3 with
                    | inl sameD =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl (lift sameD))))
                    | inr tail4 =>
                        cases tail4 with
                        | inl sameW =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lift sameW)))))
                        | inr tail5 =>
                            cases tail5 with
                            | inl sameR =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inl (lift sameR))))))
                            | inr tail6 =>
                                cases tail6 with
                                | inl sameS =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr (Or.inr (Or.inl (lift sameS)))))))
                                | inr tail7 =>
                                    cases tail7 with
                                    | inl sameH =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr (Or.inr (Or.inl (lift sameH))))))))
                                    | inr tail8 =>
                                        cases tail8 with
                                        | inl sameC =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl (lift sameC)))))))))
                                        | inr tail9 =>
                                            cases tail9 with
                                            | inl sameP =>
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
                                                                    (Or.inl
                                                                      (lift sameP))))))))))
                                            | inr sameN =>
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
                                                                      (lift sameN))))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, rfl⟩

theorem RealIntervalSealEnclosureRoute [AskSetup] [PackageSetup]
    {L U E D W R S H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory D ->
          UnaryHistory W ->
            UnaryHistory H ->
              Cont L U E ->
                Cont D W R ->
                  Cont E R S ->
                    Cont S H C ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row E ∨ hsame row R ∨ hsame row S ∨ hsame row C) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                                  hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory S ∧
                              UnaryHistory C := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro unaryL unaryU unaryD unaryW unaryH encloses dyadicRead sealRead replay pkgP pkgN
  have unaryE : UnaryHistory E :=
    unary_cont_closed unaryL unaryU encloses
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryW dyadicRead
  have unaryS : UnaryHistory S :=
    unary_cont_closed unaryE unaryR sealRead
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryS unaryH replay
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row E ∨ hsame row R ∨ hsame row S ∨ hsame row C) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨Or.inl (hsame_refl E), unaryE⟩
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameE =>
              exact Or.inl (lift sameE)
          | inr tail =>
              cases tail with
              | inl sameR =>
                  exact Or.inr (Or.inl (lift sameR))
              | inr tail =>
                  cases tail with
                  | inl sameS =>
                      exact Or.inr (Or.inr (Or.inl (lift sameS)))
                  | inr sameC =>
                      exact Or.inr (Or.inr (Or.inr (lift sameC)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameE =>
          exact Or.inr (Or.inr (Or.inl sameE))
      | inr tail =>
          cases tail with
          | inl sameR =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameR)))))
          | inr tail =>
              cases tail with
              | inl sameS =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameS))))))
              | inr sameC =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inl sameC))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN⟩
  }
  exact ⟨cert, unaryE, unaryR, unaryS, unaryC⟩

end BEDC.Derived.RealIntervalUp
