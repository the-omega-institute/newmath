import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LagrangeInversionUp

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

inductive LagrangeInversionUp : Type where
  | mk (c J a1 R B Q E H C P N : BHist) : LagrangeInversionUp

def lagrangeInversionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lagrangeInversionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lagrangeInversionEncodeBHist h

def lagrangeInversionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lagrangeInversionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lagrangeInversionDecodeBHist tail)

private theorem LagrangeInversionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lagrangeInversionFields : LagrangeInversionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LagrangeInversionUp.mk c J a1 R B Q E H C P N => [c, J, a1, R, B, Q, E, H, C, P, N]

def lagrangeInversionToEventFlow : LagrangeInversionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lagrangeInversionFields x).map lagrangeInversionEncodeBHist

private def lagrangeInversionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lagrangeInversionEventAt index rest

def lagrangeInversionFromEventFlow (ef : EventFlow) : Option LagrangeInversionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LagrangeInversionUp.mk
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 0 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 1 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 2 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 3 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 4 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 5 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 6 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 7 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 8 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 9 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 10 ef)))

private theorem LagrangeInversionTasteGate_single_carrier_alignment_round_trip
    (x : LagrangeInversionUp) :
    lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk c J a1 R B Q E H C P N =>
      change
        some
          (LagrangeInversionUp.mk
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist c))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist J))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist a1))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist R))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist B))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist Q))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist E))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist H))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist C))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist P))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist N))) =
          some (LagrangeInversionUp.mk c J a1 R B Q E H C P N)
      rw [LagrangeInversionTasteGate_single_carrier_alignment_decode_encode c,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode J,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode a1,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode R,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode B,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode Q,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode E,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode H,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode C,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode P,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode N]

private theorem lagrangeInversionToEventFlow_injective {x y : LagrangeInversionUp} :
    lagrangeInversionToEventFlow x = lagrangeInversionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) =
        lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow y) :=
    congrArg lagrangeInversionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LagrangeInversionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LagrangeInversionTasteGate_single_carrier_alignment_round_trip y)))

instance lagrangeInversionBHistCarrier : BHistCarrier LagrangeInversionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lagrangeInversionToEventFlow
  fromEventFlow := lagrangeInversionFromEventFlow

instance lagrangeInversionChapterTasteGate : ChapterTasteGate LagrangeInversionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x
    exact LagrangeInversionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lagrangeInversionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LagrangeInversionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lagrangeInversionChapterTasteGate

theorem LagrangeInversionTasteGate_single_carrier_alignment :
    (∀ h : BHist, lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist h) = h) ∧
      (∀ x : LagrangeInversionUp,
        lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x) ∧
        (∀ x y : LagrangeInversionUp,
          lagrangeInversionToEventFlow x = lagrangeInversionToEventFlow y → x = y) ∧
          lagrangeInversionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LagrangeInversionTasteGate_single_carrier_alignment_decode_encode,
      LagrangeInversionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => lagrangeInversionToEventFlow_injective heq),
      rfl⟩

theorem LagrangeInversionNameCertObligations [AskSetup] [PackageSetup]
    {c J a1 R B Q E H C P N coeffRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory c ->
      UnaryHistory J ->
        UnaryHistory a1 ->
          UnaryHistory R ->
            UnaryHistory B ->
              UnaryHistory Q ->
                UnaryHistory E ->
                  Cont c J coeffRead ->
                    Cont coeffRead a1 R ->
                      Cont R B Q ->
                        Cont Q E outputRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle outputRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row c ∨ hsame row J ∨ hsame row a1 ∨
                                      hsame row R ∨ hsame row B ∨ hsame row Q ∨
                                        hsame row E ∨ hsame row H ∨ hsame row C ∨
                                          hsame row P ∨ hsame row N ∨ hsame row coeffRead ∨
                                            hsame row outputRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont c J coeffRead ∧
                                      Cont coeffRead a1 R ∧ Cont R B Q ∧
                                        Cont Q E outputRead ∧ PkgSig bundle outputRead pkg)
                                  hsame ∧
                                UnaryHistory coeffRead ∧ UnaryHistory outputRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryC unaryJ unaryA1 _unaryR unaryB _unaryQ unaryE routeCoeff routeR routeQ
    routeOutput pPkg outputPkg
  have coeffUnary : UnaryHistory coeffRead :=
    unary_cont_closed unaryC unaryJ routeCoeff
  have unaryRFromRoute : UnaryHistory R :=
    unary_cont_closed coeffUnary unaryA1 routeR
  have unaryQFromRoute : UnaryHistory Q :=
    unary_cont_closed unaryRFromRoute unaryB routeQ
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryQFromRoute unaryE routeOutput
  have sourceAtOutput : hsame outputRead outputRead ∧ UnaryHistory outputRead :=
    ⟨hsame_refl outputRead, outputUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row c ∨ hsame row J ∨ hsame row a1 ∨ hsame row R ∨ hsame row B ∨
              hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row coeffRead ∨ hsame row outputRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont c J coeffRead ∧ Cont coeffRead a1 R ∧ Cont R B Q ∧
              Cont Q E outputRead ∧ PkgSig bundle outputRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead sourceAtOutput
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
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeCoeff, routeR, routeQ, routeOutput, outputPkg⟩
  }
  exact ⟨cert, coeffUnary, outputUnary⟩

end BEDC.Derived.LagrangeInversionUp
