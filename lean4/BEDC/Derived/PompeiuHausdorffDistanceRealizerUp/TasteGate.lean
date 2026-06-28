import BEDC.Derived.PompeiuHausdorffDistanceRealizerUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PompeiuHausdorffDistanceRealizerUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PompeiuHausdorffDistanceRealizerCarrier_namecert_obligations [AskSetup]
    [PackageSetup] {X A B H D0 D1 S V T C P N directedAB directedBA scalarRead
      vietorisRead replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory A →
        UnaryHistory B →
          UnaryHistory H →
            UnaryHistory D0 →
              UnaryHistory D1 →
                UnaryHistory S →
                  UnaryHistory V →
                    UnaryHistory T →
                      UnaryHistory C →
                        UnaryHistory P →
                          UnaryHistory N →
                            Cont X A directedAB →
                              Cont X B directedBA →
                                Cont directedAB D0 scalarRead →
                                  Cont directedBA D1 scalarRead →
                                    Cont scalarRead V vietorisRead →
                                      Cont vietorisRead C replayRead →
                                        PkgSig bundle P pkg →
                                          PkgSig bundle N pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row replayRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row X ∨ hsame row A ∨
                                                    hsame row B ∨ hsame row H ∨
                                                      hsame row D0 ∨ hsame row D1 ∨
                                                        hsame row S ∨ hsame row V ∨
                                                          hsame row T ∨ hsame row C ∨
                                                            hsame row P ∨ hsame row N ∨
                                                              hsame row replayRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧ Cont X A directedAB ∧
                                                    Cont X B directedBA ∧
                                                      Cont directedAB D0 scalarRead ∧
                                                        Cont directedBA D1 scalarRead ∧
                                                          Cont scalarRead V vietorisRead ∧
                                                            Cont vietorisRead C replayRead ∧
                                                              PkgSig bundle P pkg ∧
                                                                PkgSig bundle N pkg)
                                                hsame ∧
                                              UnaryHistory directedAB ∧
                                                UnaryHistory directedBA ∧
                                                  UnaryHistory scalarRead ∧
                                                    UnaryHistory vietorisRead ∧
                                                      UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro xUnary aUnary bUnary _hUnary d0Unary _d1Unary _sUnary vUnary _tUnary cUnary
    _pUnary _nUnary directedABRoute directedBARoute scalarABRoute scalarBARoute
    vietorisRoute replayRoute provenancePkg namePkg
  have directedABUnary : UnaryHistory directedAB :=
    unary_cont_closed xUnary aUnary directedABRoute
  have directedBAUnary : UnaryHistory directedBA :=
    unary_cont_closed xUnary bUnary directedBARoute
  have scalarUnary : UnaryHistory scalarRead :=
    unary_cont_closed directedABUnary d0Unary scalarABRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed scalarUnary vUnary vietorisRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed vietorisUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row A ∨ hsame row B ∨ hsame row H ∨ hsame row D0 ∨
              hsame row D1 ∨ hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X A directedAB ∧ Cont X B directedBA ∧
              Cont directedAB D0 scalarRead ∧ Cont directedBA D1 scalarRead ∧
                Cont scalarRead V vietorisRead ∧ Cont vietorisRead C replayRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
    pattern_sound := by
      intro _row sourceRow
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
                            (Or.inr (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, directedABRoute, directedBARoute, scalarABRoute, scalarBARoute,
          vietorisRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, directedABUnary, directedBAUnary, scalarUnary, vietorisUnary, replayUnary⟩

end BEDC.Derived.PompeiuHausdorffDistanceRealizerUp.TasteGate
