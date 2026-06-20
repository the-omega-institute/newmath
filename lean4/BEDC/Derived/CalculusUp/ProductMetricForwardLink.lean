import BEDC.Derived.CalculusUp.LimitRealHandoff

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusProductMetricForwardLink [AskSetup] [PackageSetup]
    {cauchyProduct metric stream regSeq dyadic real productRead streamRead regularRead
      dyadicRead terminalRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory cauchyProduct →
      UnaryHistory metric →
        UnaryHistory stream →
          UnaryHistory regSeq →
            UnaryHistory dyadic →
              UnaryHistory real →
                Cont cauchyProduct metric productRead →
                  Cont productRead stream streamRead →
                    Cont streamRead regSeq regularRead →
                      Cont regularRead dyadic dyadicRead →
                        Cont dyadicRead real terminalRead →
                          PkgSig bundle provenance pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row cauchyProduct ∨ hsame row metric ∨
                                    hsame row stream ∨ hsame row regSeq ∨ hsame row dyadic ∨
                                      hsame row real ∨ hsame row terminalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    Cont cauchyProduct metric productRead ∧
                                      Cont productRead stream streamRead ∧
                                        Cont streamRead regSeq regularRead ∧
                                          Cont regularRead dyadic dyadicRead ∧
                                            Cont dyadicRead real terminalRead ∧
                                              PkgSig bundle provenance pkg)
                                hsame ∧
                              UnaryHistory productRead ∧ UnaryHistory streamRead ∧
                                UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
                                  UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro cauchyUnary metricUnary streamUnary regSeqUnary dyadicUnary realUnary productRoute
    streamRoute regularRoute dyadicRoute terminalRoute provenancePkg
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed cauchyUnary metricUnary productRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed productReadUnary streamUnary streamRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed streamReadUnary regSeqUnary regularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularReadUnary dyadicUnary dyadicRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicReadUnary realUnary terminalRoute
  have sourceAtTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cauchyProduct ∨ hsame row metric ∨ hsame row stream ∨
              hsame row regSeq ∨ hsame row dyadic ∨ hsame row real ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cauchyProduct metric productRead ∧
              Cont productRead stream streamRead ∧ Cont streamRead regSeq regularRead ∧
                Cont regularRead dyadic dyadicRead ∧ Cont dyadicRead real terminalRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceAtTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, productRoute, streamRoute, regularRoute, dyadicRoute,
          terminalRoute, provenancePkg⟩
  }
  exact
    ⟨cert, productReadUnary, streamReadUnary, regularReadUnary, dyadicReadUnary,
      terminalReadUnary⟩

theorem CalculusProductMetricSealPairing [AskSetup] [PackageSetup]
    {cauchyProduct metric stream regSeq dyadic leftReal rightReal productRead streamRead
      regularRead dyadicRead leftSeal rightSeal provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory cauchyProduct →
      UnaryHistory metric →
        UnaryHistory stream →
          UnaryHistory regSeq →
            UnaryHistory dyadic →
              UnaryHistory leftReal →
                UnaryHistory rightReal →
                  Cont cauchyProduct metric productRead →
                    Cont productRead stream streamRead →
                      Cont streamRead regSeq regularRead →
                        Cont regularRead dyadic dyadicRead →
                          Cont dyadicRead leftReal leftSeal →
                            Cont dyadicRead rightReal rightSeal →
                              PkgSig bundle provenance pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      (hsame row leftSeal ∨ hsame row rightSeal) ∧
                                        UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row cauchyProduct ∨ hsame row metric ∨
                                        hsame row stream ∨ hsame row regSeq ∨
                                          hsame row dyadic ∨ hsame row leftReal ∨
                                            hsame row rightReal ∨ hsame row leftSeal ∨
                                              hsame row rightSeal)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont regularRead dyadic dyadicRead ∧
                                          Cont dyadicRead leftReal leftSeal ∧
                                            Cont dyadicRead rightReal rightSeal ∧
                                              PkgSig bundle provenance pkg)
                                    hsame ∧
                                  UnaryHistory leftSeal ∧ UnaryHistory rightSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro cauchyUnary metricUnary streamUnary regSeqUnary dyadicUnary leftRealUnary
    rightRealUnary productRoute streamRoute regularRoute dyadicRoute leftSealRoute
    rightSealRoute provenancePkg
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed cauchyUnary metricUnary productRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed productReadUnary streamUnary streamRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed streamReadUnary regSeqUnary regularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularReadUnary dyadicUnary dyadicRoute
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed dyadicReadUnary leftRealUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed dyadicReadUnary rightRealUnary rightSealRoute
  have sourceLeft :
      (fun row : BHist =>
        (hsame row leftSeal ∨ hsame row rightSeal) ∧ UnaryHistory row) leftSeal := by
    exact ⟨Or.inl (hsame_refl leftSeal), leftSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftSeal ∨ hsame row rightSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cauchyProduct ∨ hsame row metric ∨ hsame row stream ∨
              hsame row regSeq ∨ hsame row dyadic ∨ hsame row leftReal ∨
                hsame row rightReal ∨ hsame row leftSeal ∨ hsame row rightSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regularRead dyadic dyadicRead ∧
              Cont dyadicRead leftReal leftSeal ∧ Cont dyadicRead rightReal rightSeal ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leftSeal sourceLeft
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
        cases source.left with
        | inl sameLeft =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameLeft),
                unary_transport source.right sameRows⟩
        | inr sameRight =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameRight),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLeft =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inl sameLeft)))))))
      | inr sameRight =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sameRight)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, leftSealRoute, rightSealRoute, provenancePkg⟩
  }
  exact ⟨cert, leftSealUnary, rightSealUnary⟩

end BEDC.Derived.CalculusUp
