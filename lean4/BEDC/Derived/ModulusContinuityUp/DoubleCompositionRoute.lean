import BEDC.Derived.ModulusContinuityUp.CompositionRoute

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityDoubleCompositionRoute [AskSetup] [PackageSetup]
    {df kf sf gf qf rf dg kg sg gg qg rg dh kh sh gh qh rh readH readG readF
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dh →
      UnaryHistory kh →
        UnaryHistory sh →
          UnaryHistory dg →
            UnaryHistory kg →
              UnaryHistory sg →
                UnaryHistory df →
                  UnaryHistory kf →
                    UnaryHistory rf →
                      Cont dh kh readH →
                        Cont readH sh readG →
                          Cont readG dg readF →
                            Cont readF kg finalRead →
                              PkgSig bundle finalRead pkg →
                                UnaryHistory readH ∧ UnaryHistory readG ∧
                                  UnaryHistory readF ∧ UnaryHistory finalRead ∧
                                    Cont dh kh readH ∧ Cont readH sh readG ∧
                                      Cont readG dg readF ∧
                                        Cont readF kg finalRead ∧
                                          PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro dhUnary khUnary shUnary dgUnary kgUnary _sgUnary _dfUnary _kfUnary _rfUnary
    dhKhRead readHShRead readGDgRead readFKgFinal finalPkg
  have readHUnary : UnaryHistory readH :=
    unary_cont_closed dhUnary khUnary dhKhRead
  have readGUnary : UnaryHistory readG :=
    unary_cont_closed readHUnary shUnary readHShRead
  have readFUnary : UnaryHistory readF :=
    unary_cont_closed readGUnary dgUnary readGDgRead
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed readFUnary kgUnary readFKgFinal
  exact
    ⟨readHUnary, readGUnary, readFUnary, finalReadUnary, dhKhRead, readHShRead,
      readGDgRead, readFKgFinal, finalPkg⟩

end BEDC.Derived.ModulusContinuityUp
