import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EpigraphicalLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive EpigraphicalLimitUp where
  | finiteEpigraphWindowCertificate

def EpigraphicalLimitCarrierSurface [AskSetup] [PackageSetup]
    (E G M X R W H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: EpigraphicalLimitUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory E ∧ UnaryHistory G ∧ UnaryHistory M ∧ UnaryHistory X ∧ UnaryHistory R ∧
    UnaryHistory W ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EpigraphicalLimitNameCertObligations [AskSetup] [PackageSetup]
    {E G M X R W H C P N epigraphRead gammaRead moscoRead metricRead realRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphicalLimitCarrierSurface E G M X R W H C P N bundle pkg →
      Cont E W epigraphRead →
        Cont G W gammaRead →
          Cont M X moscoRead →
            Cont X R metricRead →
              Cont metricRead N realRead →
                Cont realRead C namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row E ∨ hsame row G ∨ hsame row M ∨ hsame row X ∨
                            hsame row R ∨ hsame row W ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont E W epigraphRead ∧
                            Cont G W gammaRead ∧ Cont M X moscoRead ∧
                              Cont X R metricRead ∧ Cont metricRead N realRead ∧
                                Cont realRead C namedRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory epigraphRead ∧ UnaryHistory gammaRead ∧
                        UnaryHistory moscoRead ∧ UnaryHistory metricRead ∧
                          UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: EpigraphicalLimitCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier epigraphRoute gammaRoute moscoRoute metricRoute realRoute namedRoute namedPkg
  obtain ⟨eUnary, gUnary, mUnary, xUnary, rUnary, wUnary, _hUnary, cUnary, _pUnary,
    nUnary, provenancePkg, _localNamePkg⟩ := carrier
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed eUnary wUnary epigraphRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed gUnary wUnary gammaRoute
  have moscoUnary : UnaryHistory moscoRead :=
    unary_cont_closed mUnary xUnary moscoRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed xUnary rUnary metricRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed metricUnary nUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row G ∨ hsame row M ∨ hsame row X ∨ hsame row R ∨
              hsame row W ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E W epigraphRead ∧ Cont G W gammaRead ∧
              Cont M X moscoRead ∧ Cont X R metricRead ∧ Cont metricRead N realRead ∧
                Cont realRead C namedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle namedRead pkg)
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, epigraphRoute, gammaRoute, moscoRoute, metricRoute, realRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, epigraphUnary, gammaUnary, moscoUnary, metricUnary, realUnary, namedUnary⟩

end BEDC.Derived.EpigraphicalLimitUp
