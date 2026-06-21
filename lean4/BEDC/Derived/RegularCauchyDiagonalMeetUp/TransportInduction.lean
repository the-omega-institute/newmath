import BEDC.Derived.RegularCauchyDiagonalMeetUp.SharedThresholdFactorization
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.RegularCauchyDiagonalMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalMeetTransportInduction [AskSetup] [PackageSetup]
    {M T E W Q H N mt te ew thresholdRead namedRead mt' te' ew' thresholdRead'
      namedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory N →
                hsame mt mt' →
                  hsame te te' →
                    hsame ew ew' →
                      hsame thresholdRead thresholdRead' →
                        hsame namedRead namedRead' →
                          Cont M T mt →
                            Cont mt E te →
                              Cont te W ew →
                                Cont ew Q thresholdRead →
                                  Cont thresholdRead N namedRead →
                                    PkgSig bundle H pkg →
                                      PkgSig bundle namedRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead' ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row T ∨
                                                hsame row E ∨ hsame row W ∨
                                                  hsame row Q ∨ hsame row namedRead')
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont M T mt' ∧
                                                Cont mt' E te' ∧ Cont te' W ew' ∧
                                                  Cont ew' Q thresholdRead' ∧
                                                    Cont thresholdRead' N namedRead' ∧
                                                      PkgSig bundle H pkg ∧
                                                        PkgSig bundle namedRead pkg)
                                            hsame ∧
                                          UnaryHistory namedRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryM unaryT unaryE unaryW unaryQ unaryN sameMt sameTe sameEw sameThreshold
    sameNamed mtRoute teRoute ewRoute thresholdRoute namedRoute provenancePkg namedPkg
  have mtRoute' : Cont M T mt' :=
    cont_result_hsame_transport mtRoute sameMt
  have teRoute' : Cont mt' E te' :=
    cont_hsame_transport sameMt (hsame_refl E) sameTe teRoute
  have ewRoute' : Cont te' W ew' :=
    cont_hsame_transport sameTe (hsame_refl W) sameEw ewRoute
  have thresholdRoute' : Cont ew' Q thresholdRead' :=
    cont_hsame_transport sameEw (hsame_refl Q) sameThreshold thresholdRoute
  have namedRoute' : Cont thresholdRead' N namedRead' :=
    cont_hsame_transport sameThreshold (hsame_refl N) sameNamed namedRoute
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
  have namedUnary' : UnaryHistory namedRead' :=
    unary_transport namedUnary sameNamed
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead' ⟨hsame_refl namedRead', namedUnary'⟩
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
          ⟨source.right, mtRoute', teRoute', ewRoute', thresholdRoute', namedRoute',
            provenancePkg, namedPkg⟩
    }
  · exact namedUnary'

end BEDC.Derived.RegularCauchyDiagonalMeetUp
