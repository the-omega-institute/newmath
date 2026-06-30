import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BoundaryPressureLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundaryPressureLedgerNamecertObligations [AskSetup] [PackageSetup]
    {support outer degree pressure aggregate corner transport replay provenance localName
      supportOuter degreePressure aggregateCorner ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory support →
      UnaryHistory outer →
        UnaryHistory degree →
          UnaryHistory pressure →
            UnaryHistory aggregate →
              UnaryHistory corner →
                UnaryHistory transport →
                  UnaryHistory replay →
                    Cont support outer supportOuter →
                      Cont degree pressure degreePressure →
                        Cont aggregate corner aggregateCorner →
                          Cont supportOuter degreePressure ledgerRead →
                            PkgSig bundle provenance pkg →
                              PkgSig bundle localName pkg →
                                SemanticNameCert
                                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row support ∨ hsame row outer ∨ hsame row degree ∨
                                      hsame row pressure ∨ hsame row aggregate ∨
                                        hsame row corner ∨ hsame row ledgerRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont support outer supportOuter ∧
                                      Cont degree pressure degreePressure ∧
                                        Cont aggregate corner aggregateCorner ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                  hsame ∧
                                  UnaryHistory supportOuter ∧ UnaryHistory degreePressure ∧
                                    UnaryHistory aggregateCorner ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro supportUnary outerUnary degreeUnary pressureUnary aggregateUnary cornerUnary
    _transportUnary _replayUnary supportOuterRoute degreePressureRoute aggregateCornerRoute
    ledgerRoute provenancePkg localNamePkg
  have supportOuterUnary : UnaryHistory supportOuter :=
    unary_cont_closed supportUnary outerUnary supportOuterRoute
  have degreePressureUnary : UnaryHistory degreePressure :=
    unary_cont_closed degreeUnary pressureUnary degreePressureRoute
  have aggregateCornerUnary : UnaryHistory aggregateCorner :=
    unary_cont_closed aggregateUnary cornerUnary aggregateCornerRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed supportOuterUnary degreePressureUnary ledgerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row support ∨ hsame row outer ∨ hsame row degree ∨ hsame row pressure ∨
            hsame row aggregate ∨ hsame row corner ∨ hsame row ledgerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont support outer supportOuter ∧
            Cont degree pressure degreePressure ∧ Cont aggregate corner aggregateCorner ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact unary_transport source.right sameRows
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
      exact
        ⟨source.right, supportOuterRoute, degreePressureRoute, aggregateCornerRoute,
          provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, supportOuterUnary, degreePressureUnary, aggregateCornerUnary, ledgerUnary⟩

end BEDC.Derived.BoundaryPressureLedgerUp
