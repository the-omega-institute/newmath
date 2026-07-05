import BEDC.Derived.FiniteCauchyGluingBudgetUp.Classifier

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCauchyGluingBudgetCarrier_scope [AskSetup] [PackageSetup]
    {G L T S K U V D R H C P N scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteCauchyGluingBudgetClassifier G L T S K U V D R H C P N scopedRead bundle pkg →
      Cont R N scopedRead →
        UnaryHistory G →
          UnaryHistory L →
            UnaryHistory S →
              UnaryHistory U →
                UnaryHistory V →
                  UnaryHistory N →
                    SemanticNameCert
                        (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row G ∨ hsame row L ∨ hsame row T ∨ hsame row S ∨
                            hsame row K ∨ hsame row U ∨ hsame row V ∨ hsame row D ∨
                              hsame row R ∨ hsame row scopedRead)
                        (fun row : BHist =>
                          hsame row scopedRead ∧
                            finiteCauchyGluingBudgetClassifier G L T S K U V D R H C P N
                              row bundle pkg)
                        hsame ∧
                      UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier routeScope unaryG unaryL unaryS unaryU unaryV unaryN
  obtain ⟨sameScopedN, routeGLT, routeTSK, routeKUD, routeDVR, routeHCP, namePkg⟩ :=
    classifier
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryG unaryL routeGLT
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryT unaryS routeTSK
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryK unaryU routeKUD
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryV routeDVR
  have unaryScoped : UnaryHistory scopedRead :=
    unary_cont_closed unaryR unaryN routeScope
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row L ∨ hsame row T ∨ hsame row S ∨ hsame row K ∨
              hsame row U ∨ hsame row V ∨ hsame row D ∨ hsame row R ∨
                hsame row scopedRead)
          (fun row : BHist =>
            hsame row scopedRead ∧
              finiteCauchyGluingBudgetClassifier G L T S K U V D R H C P N row bundle pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, unaryScoped⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      have rowClassifier :
          finiteCauchyGluingBudgetClassifier G L T S K U V D R H C P N _row bundle pkg :=
        ⟨hsame_trans source.left sameScopedN,
          routeGLT, routeTSK, routeKUD, routeDVR, routeHCP, namePkg⟩
      exact ⟨source.left, rowClassifier⟩
  }
  exact ⟨cert, unaryScoped⟩

end BEDC.Derived.FiniteCauchyGluingBudgetUp
