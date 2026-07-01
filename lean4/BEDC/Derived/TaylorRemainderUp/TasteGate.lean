import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaylorRemainderUp

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

inductive TaylorRemainderUp : Type where
  | mk : (D P W E Q S H C G N : BHist) -> TaylorRemainderUp

def TaylorRemainderCarrier [AskSetup] [PackageSetup]
    (D P W E Q S H C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  UnaryHistory D ∧ UnaryHistory P ∧ UnaryHistory W ∧ UnaryHistory E ∧
    UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory G ∧ UnaryHistory N ∧ Cont D P W ∧ Cont W E Q ∧
        Cont Q S H ∧ PkgSig bundle G pkg ∧ PkgSig bundle N pkg ∧ hsame N N

theorem TaylorRemainderCarrier_route_certificate [AskSetup] [PackageSetup]
    {D P W E Q S H C G N readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorRemainderCarrier D P W E Q S H C G N bundle pkg →
      Cont Q S readback →
        Cont readback N sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row D ∨ hsame row P ∨ hsame row W ∨ hsame row E ∨
                    hsame row Q ∨ hsame row S ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont D P W ∧ Cont W E Q ∧
                    Cont Q S readback ∧ Cont readback N sealRead ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readbackRoute sealRoute sealPkg
  have dUnary : UnaryHistory D := carrier.left
  have pUnary : UnaryHistory P := carrier.right.left
  have wUnary : UnaryHistory W := carrier.right.right.left
  have eUnary : UnaryHistory E := carrier.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have dpw : Cont D P W :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have weq : Cont W E Q :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed qUnary sUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary nUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row P ∨ hsame row W ∨ hsame row E ∨
              hsame row Q ∨ hsame row S ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D P W ∧ Cont W E Q ∧ Cont Q S readback ∧
              Cont readback N sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dpw, weq, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, sealReadUnary⟩

def taylorRemainderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taylorRemainderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taylorRemainderEncodeBHist h

def taylorRemainderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taylorRemainderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taylorRemainderDecodeBHist tail)

private theorem taylorRemainderDecode_encode_bhist :
    forall h : BHist, taylorRemainderDecodeBHist (taylorRemainderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def taylorRemainderToEventFlow : TaylorRemainderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TaylorRemainderUp.mk D P W E Q S H C G N =>
      [[BMark.b0],
        taylorRemainderEncodeBHist D,
        [BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        taylorRemainderEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist N]

private def taylorRemainderEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => taylorRemainderEventAtDefault index rest

def taylorRemainderFromEventFlow (ef : EventFlow) : Option TaylorRemainderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TaylorRemainderUp.mk
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 1 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 3 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 5 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 7 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 9 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 11 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 13 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 15 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 17 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 19 ef)))

private theorem taylorRemainder_round_trip :
    forall x : TaylorRemainderUp,
      taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D P W E Q S H C G N =>
      change
        some
          (TaylorRemainderUp.mk
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist D))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist P))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist W))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist E))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist Q))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist S))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist H))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist C))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist G))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist N))) =
          some (TaylorRemainderUp.mk D P W E Q S H C G N)
      rw [taylorRemainderDecode_encode_bhist D,
        taylorRemainderDecode_encode_bhist P,
        taylorRemainderDecode_encode_bhist W,
        taylorRemainderDecode_encode_bhist E,
        taylorRemainderDecode_encode_bhist Q,
        taylorRemainderDecode_encode_bhist S,
        taylorRemainderDecode_encode_bhist H,
        taylorRemainderDecode_encode_bhist C,
        taylorRemainderDecode_encode_bhist G,
        taylorRemainderDecode_encode_bhist N]

private theorem taylorRemainderToEventFlow_injective {x y : TaylorRemainderUp} :
    taylorRemainderToEventFlow x = taylorRemainderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) =
        taylorRemainderFromEventFlow (taylorRemainderToEventFlow y) :=
    congrArg taylorRemainderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (taylorRemainder_round_trip x).symm
      (Eq.trans hread (taylorRemainder_round_trip y)))

instance taylorRemainderBHistCarrier : BHistCarrier TaylorRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taylorRemainderToEventFlow
  fromEventFlow := taylorRemainderFromEventFlow

instance taylorRemainderChapterTasteGate : ChapterTasteGate TaylorRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) = some x
    exact taylorRemainder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (taylorRemainderToEventFlow_injective heq)

theorem TaylorRemainderCarrier_namecert_obligations (x : TaylorRemainderUp) :
    exists D P W E Q S H C G N : BHist,
      x = TaylorRemainderUp.mk D P W E Q S H C G N ∧
        hsame H H ∧ hsame C C ∧ hsame G G ∧ hsame N N ∧
          taylorRemainderEncodeBHist BHist.Empty = ([] : List BMark) ∧
            List.Mem (taylorRemainderEncodeBHist D) (BHistCarrier.toEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark hsame BHistCarrier
  cases x with
  | mk D P W E Q S H C G N =>
      refine
        ⟨D, P, W, E, Q, S, H, C, G, N, rfl, hsame_refl H, hsame_refl C,
          hsame_refl G, hsame_refl N, rfl, ?_⟩
      simp only [BHistCarrier.toEventFlow, taylorRemainderToEventFlow]
      exact List.Mem.tail _ (List.Mem.head _)

end BEDC.Derived.TaylorRemainderUp
