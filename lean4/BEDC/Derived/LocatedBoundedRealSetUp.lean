import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedBoundedRealSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedBoundedRealSetUp : Type where
  | mk (M I D W R E H C P N : BHist) : LocatedBoundedRealSetUp
  deriving DecidableEq

def locatedBoundedRealSetEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedBoundedRealSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedBoundedRealSetEncodeBHist h

def locatedBoundedRealSetDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedBoundedRealSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedBoundedRealSetDecodeBHist tail)

private theorem locatedBoundedRealSetDecodeEncode :
    ∀ h : BHist, locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedBoundedRealSetFields : LocatedBoundedRealSetUp → List BHist
  | LocatedBoundedRealSetUp.mk M I D W R E H C P N => [M, I, D, W, R, E, H, C, P, N]

def locatedBoundedRealSetToEventFlow : LocatedBoundedRealSetUp → EventFlow
  | x => List.map locatedBoundedRealSetEncodeBHist (locatedBoundedRealSetFields x)

private def locatedBoundedRealSetEventAt : Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedBoundedRealSetEventAt index rest

def locatedBoundedRealSetFromEventFlow : EventFlow → Option LocatedBoundedRealSetUp
  | ef =>
      some
        (LocatedBoundedRealSetUp.mk
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 0 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 1 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 2 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 3 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 4 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 5 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 6 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 7 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 8 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 9 ef)))

private theorem locatedBoundedRealSetRoundTrip :
    ∀ x : LocatedBoundedRealSetUp,
      locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x := by
  intro x
  cases x with
  | mk M I D W R E H C P N =>
      change
        some
          (LocatedBoundedRealSetUp.mk
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist M))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist I))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist D))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist W))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist R))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist E))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist H))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist C))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist P))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist N))) =
          some (LocatedBoundedRealSetUp.mk M I D W R E H C P N)
      rw [locatedBoundedRealSetDecodeEncode M,
        locatedBoundedRealSetDecodeEncode I,
        locatedBoundedRealSetDecodeEncode D,
        locatedBoundedRealSetDecodeEncode W,
        locatedBoundedRealSetDecodeEncode R,
        locatedBoundedRealSetDecodeEncode E,
        locatedBoundedRealSetDecodeEncode H,
        locatedBoundedRealSetDecodeEncode C,
        locatedBoundedRealSetDecodeEncode P,
        locatedBoundedRealSetDecodeEncode N]

private theorem locatedBoundedRealSetToEventFlowInjective {x y : LocatedBoundedRealSetUp} :
    locatedBoundedRealSetToEventFlow x = locatedBoundedRealSetToEventFlow y → x = y := by
  intro heq
  have hread :
      locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) =
        locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow y) :=
    congrArg locatedBoundedRealSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedBoundedRealSetRoundTrip x).symm
      (Eq.trans hread (locatedBoundedRealSetRoundTrip y)))

private theorem locatedBoundedRealSetFieldFaithful :
    ∀ x y : LocatedBoundedRealSetUp, locatedBoundedRealSetFields x = locatedBoundedRealSetFields y →
      x = y := by
  intro x y hfields
  cases x with
  | mk M1 I1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 I2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedBoundedRealSetBHistCarrier : BHistCarrier LocatedBoundedRealSetUp where
  toEventFlow := locatedBoundedRealSetToEventFlow
  fromEventFlow := locatedBoundedRealSetFromEventFlow

instance locatedBoundedRealSetChapterTasteGate : ChapterTasteGate LocatedBoundedRealSetUp where
  round_trip := by
    intro x
    change locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x
    exact locatedBoundedRealSetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedBoundedRealSetToEventFlowInjective heq)

instance locatedBoundedRealSetFieldFaithfulInstance : FieldFaithful LocatedBoundedRealSetUp where
  fields := locatedBoundedRealSetFields
  field_faithful := locatedBoundedRealSetFieldFaithful

instance locatedBoundedRealSetNontrivial : Nontrivial LocatedBoundedRealSetUp where
  witness_pair :=
    ⟨LocatedBoundedRealSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedBoundedRealSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedBoundedRealSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedBoundedRealSetUp) ∧
      Nonempty (FieldFaithful LocatedBoundedRealSetUp) ∧
      Nonempty (Nontrivial LocatedBoundedRealSetUp) ∧
      (∀ h : BHist,
        locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist h) = h) ∧
      (∀ x : LocatedBoundedRealSetUp,
        locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x) ∧
      (∀ x y : LocatedBoundedRealSetUp,
        locatedBoundedRealSetToEventFlow x = locatedBoundedRealSetToEventFlow y → x = y) ∧
      locatedBoundedRealSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  constructor
  · exact ⟨locatedBoundedRealSetChapterTasteGate⟩
  · constructor
    · exact ⟨locatedBoundedRealSetFieldFaithfulInstance⟩
    · constructor
      · exact ⟨locatedBoundedRealSetNontrivial⟩
      · constructor
        · exact locatedBoundedRealSetDecodeEncode
        · constructor
          · exact locatedBoundedRealSetRoundTrip
          · constructor
            · intro x y heq
              exact locatedBoundedRealSetToEventFlowInjective heq
            · rfl

theorem LocatedBoundedRealSetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (B : LocatedBoundedRealSetUp)
    {M I D W R E H C P N membershipRead intervalRead dyadicRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    locatedBoundedRealSetFields B = [M, I, D, W, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory I ->
          UnaryHistory D ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory E ->
                  Cont M W membershipRead ->
                    Cont I D intervalRead ->
                      Cont intervalRead R dyadicRead ->
                        Cont dyadicRead E realSeal ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row I ∨ hsame row D ∨ hsame row W ∨
                                    hsame row R ∨ hsame row E ∨ Cont M W membershipRead ∨
                                      Cont I D intervalRead ∨ Cont intervalRead R dyadicRead ∨
                                        Cont dyadicRead E realSeal)
                                (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
                                hsame ∧
                              UnaryHistory membershipRead ∧ UnaryHistory intervalRead ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro fieldEq mUnary iUnary dUnary wUnary rUnary eUnary membershipRoute intervalRoute
    dyadicRoute realSealRoute provenancePkg
  cases B with
  | mk MB IB DB WB RB EB HB CB PB NB =>
      cases fieldEq
      have membershipUnary : UnaryHistory membershipRead :=
        unary_cont_closed mUnary wUnary membershipRoute
      have intervalUnary : UnaryHistory intervalRead :=
        unary_cont_closed iUnary dUnary intervalRoute
      have dyadicUnary : UnaryHistory dyadicRead :=
        unary_cont_closed intervalUnary rUnary dyadicRoute
      have realSealUnary : UnaryHistory realSeal :=
        unary_cont_closed dyadicUnary eUnary realSealRoute
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row I ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨
                  hsame row E ∨ Cont M W membershipRead ∨ Cont I D intervalRead ∨
                    Cont intervalRead R dyadicRead ∨ Cont dyadicRead E realSeal)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
              hsame := {
        core := {
          carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
            intro _row other sameRows source
            exact
              ⟨hsame_trans (hsame_symm sameRows) source.left,
                unary_transport source.right sameRows⟩
        }
        pattern_sound := by
          intro _row _source
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr realSealRoute))))))))
        ledger_sound := by
          intro _row source
          exact ⟨provenancePkg, source.left⟩
      }
      exact ⟨cert, membershipUnary, intervalUnary, dyadicUnary, realSealUnary⟩

end BEDC.Derived.LocatedBoundedRealSetUp
