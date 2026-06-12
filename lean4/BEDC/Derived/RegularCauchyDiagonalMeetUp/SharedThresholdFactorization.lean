import BEDC.Derived.RegularCauchyDiagonalMeetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalMeetSharedThresholdFactorization [AskSetup] [PackageSetup]
    {T M E W Q _H _C P N mt te ew thresholdRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory N →
                Cont M T mt →
                  Cont mt E te →
                    Cont te W ew →
                      Cont ew Q thresholdRead →
                        Cont thresholdRead N namedRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle namedRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row T ∨ hsame row E ∨
                                      hsame row W ∨ hsame row Q ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M T mt ∧ Cont mt E te ∧
                                      Cont te W ew ∧ Cont ew Q thresholdRead ∧
                                        Cont thresholdRead N namedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                                  hsame ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryM unaryT unaryE unaryW unaryQ unaryN mtRoute teRoute ewRoute thresholdRoute
    namedRoute provenancePkg namedPkg
  have mtUnary : UnaryHistory mt :=
    unary_cont_closed unaryM unaryT mtRoute
  have teUnary : UnaryHistory te :=
    unary_cont_closed mtUnary unaryE teRoute
  have ewUnary : UnaryHistory ew :=
    unary_cont_closed teUnary unaryW ewRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed ewUnary unaryQ thresholdRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed thresholdUnary unaryN namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, mtRoute, teRoute, ewRoute, thresholdRoute, namedRoute,
            provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.RegularCauchyDiagonalMeetUp
