import BEDC.Derived.BanachSpaceUp

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceScopedCompletionRoute [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normRead metricRead cauchyRead completionRead
      toleranceRead separatedRead transportRead replayRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V →
      UnaryHistory N →
        UnaryHistory M →
          UnaryHistory Q →
            UnaryHistory S →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory Z →
                    UnaryHistory H →
                      UnaryHistory C →
                        UnaryHistory L →
                          Cont V N normRead →
                            Cont normRead M metricRead →
                              Cont Q S cauchyRead →
                                Cont cauchyRead R completionRead →
                                  Cont completionRead E toleranceRead →
                                    Cont toleranceRead Z separatedRead →
                                      Cont separatedRead H transportRead →
                                        Cont transportRead C replayRead →
                                          Cont replayRead L scopedRead →
                                            PkgSig bundle P pkg →
                                              PkgSig bundle scopedRead pkg →
                                                SemanticNameCert
                                                    (fun row : BHist =>
                                                      hsame row scopedRead ∧
                                                        UnaryHistory row)
                                                    (fun row : BHist =>
                                                      hsame row V ∨ hsame row N ∨
                                                        hsame row M ∨ hsame row Q ∨
                                                          hsame row S ∨ hsame row R ∨
                                                            hsame row E ∨
                                                              hsame row Z ∨
                                                                hsame row H ∨
                                                                  hsame row C ∨
                                                                    hsame row L ∨
                                                                      hsame row
                                                                        scopedRead)
                                                    (fun row : BHist =>
                                                      UnaryHistory row ∧
                                                        Cont V N normRead ∧
                                                          Cont normRead M metricRead ∧
                                                            Cont Q S cauchyRead ∧
                                                              Cont cauchyRead R
                                                                  completionRead ∧
                                                                Cont completionRead E
                                                                    toleranceRead ∧
                                                                  Cont toleranceRead Z
                                                                      separatedRead ∧
                                                                    Cont separatedRead H
                                                                        transportRead ∧
                                                                      Cont transportRead C
                                                                          replayRead ∧
                                                                        Cont replayRead L
                                                                            scopedRead ∧
                                                                          PkgSig bundle
                                                                            scopedRead
                                                                            pkg)
                                                    hsame ∧
                                                  UnaryHistory normRead ∧
                                                    UnaryHistory metricRead ∧
                                                      UnaryHistory cauchyRead ∧
                                                        UnaryHistory completionRead ∧
                                                          UnaryHistory toleranceRead ∧
                                                            UnaryHistory separatedRead ∧
                                                              UnaryHistory transportRead ∧
                                                                UnaryHistory replayRead ∧
                                                                  UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro unaryV unaryN unaryM unaryQ unaryS unaryR unaryE unaryZ unaryH unaryC unaryL
    normRoute metricRoute cauchyRoute completionRoute toleranceRoute separatedRoute
    transportRoute replayRoute scopedRoute _provenancePkg scopedPkg
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed unaryV unaryN normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary unaryM metricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unaryQ unaryS cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary unaryR completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary unaryE toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary unaryZ separatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed separatedUnary unaryH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary unaryC replayRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed replayUnary unaryL scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row L ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N normRead ∧ Cont normRead M metricRead ∧
              Cont Q S cauchyRead ∧ Cont cauchyRead R completionRead ∧
                Cont completionRead E toleranceRead ∧
                  Cont toleranceRead Z separatedRead ∧
                    Cont separatedRead H transportRead ∧
                      Cont transportRead C replayRead ∧
                        Cont replayRead L scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopedRead sourceScoped
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left))))))))))
      ledger_sound := by
        intro row source
        exact
          ⟨source.right, normRoute, metricRoute, cauchyRoute, completionRoute,
            toleranceRoute, separatedRoute, transportRoute, replayRoute, scopedRoute,
              scopedPkg⟩
    }
  exact
    ⟨cert, normUnary, metricUnary, cauchyUnary, completionUnary, toleranceUnary,
      separatedUnary, transportUnary, replayUnary, scopedUnary⟩

end BEDC.Derived.BanachSpaceUp
