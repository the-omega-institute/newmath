import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeakTopologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeakTopologyNamecertObligations [AskSetup] [PackageSetup]
    {source functionals neighborhood testWindow scalar _transport _replay provenance localName
      observationRead scalarRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory functionals →
        UnaryHistory neighborhood →
          UnaryHistory testWindow →
            UnaryHistory scalar →
              Cont source functionals observationRead →
                Cont observationRead neighborhood scalarRead →
                  Cont testWindow scalar scalarRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row scalarRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row functionals ∨
                                hsame row neighborhood ∨ hsame row testWindow ∨
                                  hsame row scalar ∨ hsame row scalarRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory observationRead ∧ UnaryHistory scalarRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro sourceUnary functionalsUnary neighborhoodUnary _testWindowUnary _scalarUnary
    sourceFunctionalsObservation observationNeighborhoodScalar _testWindowScalarScalar
    provenancePkg localNamePkg
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed sourceUnary functionalsUnary sourceFunctionalsObservation
  have scalarReadUnary : UnaryHistory scalarRead :=
    unary_cont_closed observationUnary neighborhoodUnary observationNeighborhoodScalar
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scalarRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row functionals ∨ hsame row neighborhood ∨
              hsame row testWindow ∨ hsame row scalar ∨ hsame row scalarRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scalarRead ⟨hsame_refl scalarRead, scalarReadUnary⟩
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
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, observationUnary, scalarReadUnary⟩

end BEDC.Derived.WeakTopologyUp
