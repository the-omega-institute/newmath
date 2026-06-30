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

theorem BanachSpaceNormedLinearCompleteMetricRoute [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normRead metricRead completionRead separatedRead
      localRead : BHist}
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
                        Cont V N normRead ->
                          Cont normRead M metricRead ->
                            Cont Q S completionRead ->
                              Cont completionRead R separatedRead ->
                                Cont separatedRead Z localRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle L pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row localRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row V ∨ hsame row N ∨ hsame row M ∨
                                              hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                                hsame row Z ∨ hsame row localRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont V N normRead ∧
                                              Cont normRead M metricRead ∧
                                                Cont Q S completionRead ∧
                                                  Cont completionRead R separatedRead ∧
                                                    Cont separatedRead Z localRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle L pkg)
                                          hsame ∧
                                        UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                                          UnaryHistory completionRead ∧
                                            UnaryHistory separatedRead ∧
                                              UnaryHistory localRead ∧
                                                banachSpaceFields
                                                    (BanachSpaceUp.mk
                                                      V N M Q S R E Z H C P L) =
                                                  [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory BanachSpaceUp
  intro vUnary nUnary mUnary qUnary sUnary rUnary _eUnary zUnary _hUnary _cUnary
    normRoute metricRoute completionRoute separatedRoute localRoute provenancePkg localPkg
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary nUnary normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary mUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed qUnary sUnary completionRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionUnary rUnary separatedRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed separatedUnary zUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row Z ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N normRead ∧ Cont normRead M metricRead ∧
              Cont Q S completionRead ∧ Cont completionRead R separatedRead ∧
                Cont separatedRead Z localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, normRoute, metricRoute, completionRoute, separatedRoute,
          localRoute, provenancePkg, localPkg⟩
  }
  exact
    ⟨cert, normUnary, metricUnary, completionUnary, separatedUnary, localUnary, rfl⟩

end BEDC.Derived.BanachSpaceUp
