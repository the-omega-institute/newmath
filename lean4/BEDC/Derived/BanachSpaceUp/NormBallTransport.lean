import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_norm_ball_transport [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normRead metricRead cauchyRead completionRead
      separatedRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory M ->
          UnaryHistory Q ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory Z ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory L ->
                          Cont V N normRead ->
                            Cont normRead M metricRead ->
                              Cont Q S cauchyRead ->
                                Cont cauchyRead R completionRead ->
                                  Cont completionRead Z separatedRead ->
                                    Cont H C replayRead ->
                                      Cont replayRead L namedRead ->
                                        PkgSig bundle P pkg ->
                                          PkgSig bundle L pkg ->
                                            SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row namedRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row V ∨ hsame row N ∨ hsame row M ∨
                                                  hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                                    hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                                      hsame row C ∨ hsame row P ∨ hsame row L ∨
                                                        hsame row namedRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont V N normRead ∧
                                                  Cont normRead M metricRead ∧
                                                    Cont Q S cauchyRead ∧
                                                      Cont cauchyRead R completionRead ∧
                                                        Cont completionRead Z separatedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle L pkg)
                                              hsame ∧
                                            UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                                              UnaryHistory cauchyRead ∧
                                                UnaryHistory completionRead ∧
                                                  UnaryHistory separatedRead ∧
                                                    UnaryHistory replayRead ∧
                                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro vUnary nUnary mUnary qUnary sUnary rUnary _eUnary zUnary hUnary cUnary lUnary normRoute
    metricRoute cauchyRoute completionRoute separatedRoute replayRoute namedRoute provenancePkg
    localPkg
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary nUnary normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary mUnary metricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionUnary zUnary separatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary lUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N normRead ∧ Cont normRead M metricRead ∧
              Cont Q S cauchyRead ∧ Cont cauchyRead R completionRead ∧
                Cont completionRead Z separatedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, normRoute, metricRoute, cauchyRoute, completionRoute, separatedRoute,
          provenancePkg, localPkg⟩
  }
  exact
    ⟨cert, normUnary, metricUnary, cauchyUnary, completionUnary, separatedUnary, replayUnary,
      namedUnary⟩

end BEDC.Derived.BanachSpaceUp
