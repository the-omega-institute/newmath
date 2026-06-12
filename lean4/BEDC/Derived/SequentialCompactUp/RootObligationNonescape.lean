import BEDC.Derived.SequentialCompactUp.RootObligationSurface

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRootObligationNonescape [AskSetup] [PackageSetup]
    {K _B S W R E _H _C P N windowRead clusterRead readbackRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory S ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                Cont K S windowRead ->
                  Cont windowRead W clusterRead ->
                    Cont clusterRead R readbackRead ->
                      Cont readbackRead E sealRead ->
                        Cont sealRead N namedRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row K ∨ hsame row S ∨ hsame row W ∨
                                      hsame row R ∨ hsame row E ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont K S windowRead ∧
                                      Cont windowRead W clusterRead ∧
                                        Cont clusterRead R readbackRead ∧
                                          Cont readbackRead E sealRead ∧
                                            Cont sealRead N namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryK unaryS unaryW unaryR unaryE unaryN windowRoute clusterRoute readbackRoute
    sealRoute namedRoute provenancePkg namedPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryK unaryS windowRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed windowUnary unaryW clusterRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed clusterUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  constructor
  · exact {
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
                  (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, windowRoute, clusterRoute, readbackRoute, sealRoute,
            namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.SequentialCompactUp
