import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FocusedLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FocusedLedgerUp : Type where
  | mk :
      (I H T F S D G R J Q rho A C P N : BHist) →
        FocusedLedgerUp
  deriving DecidableEq

def focusedLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: focusedLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: focusedLedgerEncodeBHist h

def focusedLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (focusedLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (focusedLedgerDecodeBHist tail)

theorem focusedLedgerDecode_encode_bhist :
    ∀ h : BHist, focusedLedgerDecodeBHist (focusedLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def focusedLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => focusedLedgerRawAt n rest

private theorem focusedLedger_mk_congr
    {I I' H H' T T' F F' S S' D D' G G' R R' J J' Q Q' rho rho'
        A A' C C' P P' N N' : BHist}
    (hI : I' = I)
    (hH : H' = H)
    (hT : T' = T)
    (hF : F' = F)
    (hS : S' = S)
    (hD : D' = D)
    (hG : G' = G)
    (hR : R' = R)
    (hJ : J' = J)
    (hQ : Q' = Q)
    (hrho : rho' = rho)
    (hA : A' = A)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    FocusedLedgerUp.mk I' H' T' F' S' D' G' R' J' Q' rho' A' C' P' N' =
      FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hH
  cases hT
  cases hF
  cases hS
  cases hD
  cases hG
  cases hR
  cases hJ
  cases hQ
  cases hrho
  cases hA
  cases hC
  cases hP
  cases hN
  rfl

def focusedLedgerToEventFlow : FocusedLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N =>
      [focusedLedgerEncodeBHist I,
        focusedLedgerEncodeBHist H,
        focusedLedgerEncodeBHist T,
        focusedLedgerEncodeBHist F,
        focusedLedgerEncodeBHist S,
        focusedLedgerEncodeBHist D,
        focusedLedgerEncodeBHist G,
        focusedLedgerEncodeBHist R,
        focusedLedgerEncodeBHist J,
        focusedLedgerEncodeBHist Q,
        focusedLedgerEncodeBHist rho,
        focusedLedgerEncodeBHist A,
        focusedLedgerEncodeBHist C,
        focusedLedgerEncodeBHist P,
        focusedLedgerEncodeBHist N]

def focusedLedgerFromEventFlow : EventFlow → Option FocusedLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FocusedLedgerUp.mk
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 0 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 1 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 2 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 3 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 4 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 5 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 6 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 7 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 8 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 9 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 10 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 11 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 12 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 13 ef))
        (focusedLedgerDecodeBHist (focusedLedgerRawAt 14 ef)))

def focusedLedgerFields : FocusedLedgerUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N =>
      [I, H, T, F, S, D, G, R, J, Q, rho, A, C, P, N]

theorem focusedLedger_round_trip :
    ∀ x : FocusedLedgerUp,
      focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I H T F S D G R J Q rho A C P N =>
      exact
        congrArg some
          (focusedLedger_mk_congr
            (focusedLedgerDecode_encode_bhist I)
            (focusedLedgerDecode_encode_bhist H)
            (focusedLedgerDecode_encode_bhist T)
            (focusedLedgerDecode_encode_bhist F)
            (focusedLedgerDecode_encode_bhist S)
            (focusedLedgerDecode_encode_bhist D)
            (focusedLedgerDecode_encode_bhist G)
            (focusedLedgerDecode_encode_bhist R)
            (focusedLedgerDecode_encode_bhist J)
            (focusedLedgerDecode_encode_bhist Q)
            (focusedLedgerDecode_encode_bhist rho)
            (focusedLedgerDecode_encode_bhist A)
            (focusedLedgerDecode_encode_bhist C)
            (focusedLedgerDecode_encode_bhist P)
            (focusedLedgerDecode_encode_bhist N))

theorem focusedLedgerToEventFlow_injective :
    ∀ x y : FocusedLedgerUp,
      focusedLedgerToEventFlow x = focusedLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hxy
  have optionEq : some x = some y := by
    calc
      some x = focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) :=
        (focusedLedger_round_trip x).symm
      _ = focusedLedgerFromEventFlow (focusedLedgerToEventFlow y) :=
        congrArg focusedLedgerFromEventFlow hxy
      _ = some y := focusedLedger_round_trip y
  exact Option.some.inj optionEq

instance focusedLedgerBHistCarrier : BHistCarrier FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := focusedLedgerToEventFlow
  fromEventFlow := focusedLedgerFromEventFlow

instance focusedLedgerChapterTasteGate : ChapterTasteGate FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change focusedLedgerFromEventFlow (focusedLedgerToEventFlow x) = some x
    exact focusedLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (focusedLedgerToEventFlow_injective x y heq)

instance focusedLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FocusedLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FocusedLedgerUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FocusedLedgerUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

instance focusedLedgerFieldFaithful : FieldFaithful FocusedLedgerUp where
  fields := focusedLedgerFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk I1 H1 T1 F1 S1 D1 G1 R1 J1 Q1 rho1 A1 C1 P1 N1 =>
        cases y with
        | mk I2 H2 T2 F2 S2 D2 G2 R2 J2 Q2 rho2 A2 C2 P2 N2 =>
            injection h with hI t1
            injection t1 with hH t2
            injection t2 with hT t3
            injection t3 with hF t4
            injection t4 with hS t5
            injection t5 with hD t6
            injection t6 with hG t7
            injection t7 with hR t8
            injection t8 with hJ t9
            injection t9 with hQ t10
            injection t10 with hrho t11
            injection t11 with hA t12
            injection t12 with hC t13
            injection t13 with hP t14
            injection t14 with hN _
            cases hI
            cases hH
            cases hT
            cases hF
            cases hS
            cases hD
            cases hG
            cases hR
            cases hJ
            cases hQ
            cases hrho
            cases hA
            cases hC
            cases hP
            cases hN
            rfl

def taste_gate : ChapterTasteGate FocusedLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  focusedLedgerChapterTasteGate

theorem FocusedLedgerNameCert_obligation_surface [AskSetup] [PackageSetup]
    {I H T F S D G R J Q rho A C P N focusRead digestRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F S focusRead →
      Cont D G digestRead →
        Cont A C auditRead →
          PkgSig bundle auditRead pkg →
            List.Mem (focusedLedgerEncodeBHist F)
                (focusedLedgerToEventFlow
                  (FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N)) ∧
              List.Mem (focusedLedgerEncodeBHist D)
                (focusedLedgerToEventFlow
                  (FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N)) ∧
              List.Mem (focusedLedgerEncodeBHist A)
                (focusedLedgerToEventFlow
                  (FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N)) ∧
              List.Mem (focusedLedgerEncodeBHist N)
                (focusedLedgerToEventFlow
                  (FocusedLedgerUp.mk I H T F S D G R J Q rho A C P N)) ∧
              Cont F S focusRead ∧
              Cont D G digestRead ∧
              Cont A C auditRead ∧
              PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont PkgSig ProbeBundle Pkg
  intro focusRoute digestRoute auditRoute pkgRoute
  constructor
  · unfold focusedLedgerToEventFlow
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · constructor
    · unfold focusedLedgerToEventFlow
      exact
        List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    · constructor
      · unfold focusedLedgerToEventFlow
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _ (List.Mem.head _)))))))))))
      · constructor
        · unfold focusedLedgerToEventFlow
          exact
            List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _ (List.Mem.head _))))))))))))))
        · exact ⟨focusRoute, digestRoute, auditRoute, pkgRoute⟩

end BEDC.Derived.FocusedLedgerUp
