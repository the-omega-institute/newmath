import BEDC.Derived.IntervalBisectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IntervalBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntervalBisectionNamecertObligations [AskSetup] [PackageSetup]
    {I M L R D S Q E H C P N midpointRead leftRead rightRead dyadicRead readbackRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory R ∧
        UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory E ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont I M midpointRead →
        Cont midpointRead L leftRead →
          Cont midpointRead R rightRead →
            Cont L R dyadicRead →
              Cont S Q readbackRead →
                Cont dyadicRead readbackRead sealRead →
                  Cont sealRead N namedRead →
                    PkgSig bundle namedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row I ∨ hsame row M ∨ hsame row L ∨ hsame row R ∨
                              hsame row D ∨ hsame row S ∨ hsame row Q ∨ hsame row E ∨
                                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                  hsame row namedRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
                          hsame ∧
                        UnaryHistory midpointRead ∧ UnaryHistory leftRead ∧
                          UnaryHistory rightRead ∧ UnaryHistory dyadicRead ∧
                            UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro rows midpointRoute leftRoute rightRoute dyadicRoute readbackRoute sealRoute namedRoute
    pkgNamed
  rcases rows with
    ⟨unaryI, unaryM, unaryL, unaryR, _unaryD, unaryS, unaryQ, _unaryE, _unaryH,
      _unaryC, _unaryP, unaryN, _pkgP, _pkgN⟩
  have unaryMidpoint : UnaryHistory midpointRead :=
    unary_cont_closed unaryI unaryM midpointRoute
  have unaryLeft : UnaryHistory leftRead :=
    unary_cont_closed unaryMidpoint unaryL leftRoute
  have unaryRight : UnaryHistory rightRead :=
    unary_cont_closed unaryMidpoint unaryR rightRoute
  have unaryDyadic : UnaryHistory dyadicRead :=
    unary_cont_closed unaryL unaryR dyadicRoute
  have unaryReadback : UnaryHistory readbackRead :=
    unary_cont_closed unaryS unaryQ readbackRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryDyadic unaryReadback sealRoute
  have unaryNamed : UnaryHistory namedRead :=
    unary_cont_closed unarySeal unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row M ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨
              hsame row S ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, unaryNamed⟩
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
        exact ⟨sourceRow.right, pkgNamed⟩
    }
  exact
    ⟨cert, unaryMidpoint, unaryLeft, unaryRight, unaryDyadic, unaryReadback, unarySeal,
      unaryNamed⟩

theorem IntervalBisectionEndpointTransport [AskSetup] [PackageSetup]
    {I M L R D S Q E H C P N parentEndpoint midpointEndpoint leftEndpoint
      rightEndpoint : BHist} :
    (UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory R ∧
        UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N) →
      Cont I M midpointEndpoint →
        Cont I L leftEndpoint →
          Cont M R rightEndpoint →
            Cont leftEndpoint rightEndpoint parentEndpoint →
              UnaryHistory midpointEndpoint ∧ UnaryHistory leftEndpoint ∧
                UnaryHistory rightEndpoint ∧ UnaryHistory parentEndpoint ∧
                  Cont I M midpointEndpoint ∧ Cont I L leftEndpoint ∧
                    Cont M R rightEndpoint ∧ Cont leftEndpoint rightEndpoint parentEndpoint := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro rows midpointRoute leftRoute rightRoute parentRoute
  rcases rows with
    ⟨unaryI, unaryM, unaryL, unaryR, _unaryD, _unaryH, _unaryC, _unaryN⟩
  have unaryMidpoint : UnaryHistory midpointEndpoint :=
    unary_cont_closed unaryI unaryM midpointRoute
  have unaryLeft : UnaryHistory leftEndpoint :=
    unary_cont_closed unaryI unaryL leftRoute
  have unaryRight : UnaryHistory rightEndpoint :=
    unary_cont_closed unaryM unaryR rightRoute
  have unaryParent : UnaryHistory parentEndpoint :=
    unary_cont_closed unaryLeft unaryRight parentRoute
  exact
    ⟨unaryMidpoint, unaryLeft, unaryRight, unaryParent, midpointRoute, leftRoute,
      rightRoute, parentRoute⟩

end BEDC.Derived.IntervalBisectionUp
