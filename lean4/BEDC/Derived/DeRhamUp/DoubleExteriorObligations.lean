import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamDoubleExteriorPacket_root_carrier_obligation
    {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      SemanticNameCert
        (fun b : BHist => DeRhamBoundary d b ∧ hsame b zero ∧ hsame (d eta) BHist.Empty)
        (fun b : BHist => DeRhamBoundary d b ∧ hsame b zero)
        (fun b : BHist => DeRhamBoundary d b ∧ hsame (d eta) BHist.Empty)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) ∧
        DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame zero BHist.Empty := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet
  have sourceTheta :
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty :=
    And.intro boundary.right.left (And.intro boundary.left boundary.right.right)
  have carrierRespects :
      forall {b c : BHist},
        DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c ->
          DeRhamBoundary d b ∧ hsame b zero ∧ hsame (d eta) BHist.Empty ->
            DeRhamBoundary d c ∧ hsame c zero ∧ hsame (d eta) BHist.Empty := by
    intro b c classified sourceB
    exact And.intro classified.right.left
      (And.intro (hsame_trans (hsame_symm classified.right.right) sourceB.right.left)
        sourceB.right.right)
  have core :
      NameCert
        (fun b : BHist => DeRhamBoundary d b ∧ hsame b zero ∧ hsame (d eta) BHist.Empty)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) := {
    carrier_inhabited := Exists.intro theta sourceTheta
    equiv_refl := by
      intro b sourceB
      exact And.intro sourceB.left (And.intro sourceB.left (hsame_refl b))
    equiv_symm := by
      intro b c classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro b c r classifiedBC classifiedCR
      exact And.intro classifiedBC.left
        (And.intro classifiedCR.right.left
          (hsame_trans classifiedBC.right.right classifiedCR.right.right))
    carrier_respects_equiv := by
      intro b c classified sourceB
      exact carrierRespects classified sourceB
  }
  have cert :
      SemanticNameCert
        (fun b : BHist => DeRhamBoundary d b ∧ hsame b zero ∧ hsame (d eta) BHist.Empty)
        (fun b : BHist => DeRhamBoundary d b ∧ hsame b zero)
        (fun b : BHist => DeRhamBoundary d b ∧ hsame (d eta) BHist.Empty)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) := {
    core := core
    pattern_sound := by
      intro b sourceB
      exact And.intro sourceB.left sourceB.right.left
    ledger_sound := by
      intro b sourceB
      exact And.intro sourceB.left sourceB.right.right
  }
  exact And.intro cert
    (And.intro boundary.right.left
      (And.intro boundary.left packet.right.right.right.right))

theorem DeRhamDoubleExteriorPacket_bridge_input_source_scope
    {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      exists inputLedger zeroLedger : BHist,
        Cont omega eta inputLedger ∧ Cont (d eta) zero zeroLedger ∧
          hsame inputLedger (append omega eta) ∧ hsame zeroLedger BHist.Empty ∧
            DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty := by
  intro packet
  let inputLedger := append omega eta
  let zeroLedger := append (d eta) zero
  have boundary := DeRhamDoubleExteriorPacket_boundary packet
  have inputCont : Cont omega eta inputLedger := by
    rfl
  have zeroCont : Cont (d eta) zero zeroLedger := by
    rfl
  have zeroLedgerEmpty : hsame zeroLedger BHist.Empty :=
    append_eq_empty_iff.mpr
      (And.intro boundary.right.right packet.right.right.right.right)
  exact Exists.intro inputLedger
    (Exists.intro zeroLedger
      (And.intro inputCont
        (And.intro zeroCont
          (And.intro inputCont
            (And.intro zeroLedgerEmpty
              (And.intro boundary.right.left
                (And.intro boundary.left boundary.right.right)))))))

end BEDC.Derived.DeRhamUp
