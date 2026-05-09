import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DeRhamStandardBoundaryBridgePacket_root_cocycle_ledger_threshold
    {d : BHist -> BHist} {omega eta theta zero provenance bridge cocycleLedger : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      Cont (d eta) zero cocycleLedger ->
        SemanticNameCert (fun h : BHist => hsame h (d eta))
            (fun h : BHist => hsame h (d eta))
            (fun h : BHist => hsame h (d eta)) hsame ∧
          hsame (d eta) BHist.Empty ∧ UnaryHistory cocycleLedger ∧
            hsame cocycleLedger BHist.Empty ∧ DeRhamBoundary d theta ∧
              Cont provenance theta bridge := by
  intro packet ledgerCont
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet.left
  have derivativeEmpty : hsame (d eta) BHist.Empty := boundaryRows.right.right
  have zeroEmpty : hsame zero BHist.Empty := packet.left.right.right.right.right
  have ledgerEmpty : hsame cocycleLedger BHist.Empty := by
    cases ledgerCont
    exact append_eq_empty_iff.mpr (And.intro derivativeEmpty zeroEmpty)
  have ledgerUnary : UnaryHistory cocycleLedger := by
    cases ledgerEmpty
    exact unary_empty
  have cert :
      SemanticNameCert (fun h : BHist => hsame h (d eta))
        (fun h : BHist => hsame h (d eta))
        (fun h : BHist => hsame h (d eta)) hsame := {
    core := {
      carrier_inhabited := Exists.intro (d eta) (hsame_refl (d eta))
      equiv_refl := by
        intro h _sameEndpoint
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sameEndpoint
        exact hsame_trans (hsame_symm sameHK) sameEndpoint
    }
    pattern_sound := by
      intro _h sameEndpoint
      exact sameEndpoint
    ledger_sound := by
      intro _h sameEndpoint
      exact sameEndpoint
  }
  exact And.intro cert
    (And.intro derivativeEmpty
      (And.intro ledgerUnary
        (And.intro ledgerEmpty (And.intro boundaryRows.right.left packet.right))))

end BEDC.Derived.DeRhamUp
