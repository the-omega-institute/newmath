import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_streamname_pullback_route [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow streamRead dyadicRead regseqRead realRead pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont request windows streamRead →
        Cont streamRead dyadic dyadicRead →
          Cont dyadicRead handoff regseqRead →
            Cont regseqRead realSeal realRead →
              Cont realRead selector pullbackRead →
                PkgSig bundle pullbackRead pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                          disclosure transport route provenance nameRow bundle pkg ∧
                        (hsame row streamRead ∨ hsame row dyadicRead ∨
                          hsame row regseqRead ∨ hsame row realRead ∨
                            hsame row pullbackRead))
                    (fun row : BHist =>
                      Cont request windows streamRead ∧
                        Cont streamRead dyadic dyadicRead ∧
                          Cont dyadicRead handoff regseqRead ∧
                            Cont regseqRead realSeal realRead ∧
                              Cont realRead selector pullbackRead ∧
                                (hsame row streamRead ∨ hsame row dyadicRead ∨
                                  hsame row regseqRead ∨ hsame row realRead ∨
                                    hsame row pullbackRead))
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle pullbackRead pkg)
                    hsame ∧
                    UnaryHistory pullbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier requestWindowsStream streamDyadicRead dyadicHandoffRegseq
    regseqRealSealRead realReadSelectorPullback pullbackPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed carrier.request_unary carrier.windows_unary requestWindowsStream
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary carrier.dyadic_unary streamDyadicRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicReadUnary carrier.handoff_unary dyadicHandoffRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary carrier.realSeal_unary regseqRealSealRead
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed realReadUnary carrier.selector_unary realReadSelectorPullback
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
              disclosure transport route provenance nameRow bundle pkg ∧
            (hsame row streamRead ∨ hsame row dyadicRead ∨ hsame row regseqRead ∨
              hsame row realRead ∨ hsame row pullbackRead))
        (fun row : BHist =>
          Cont request windows streamRead ∧ Cont streamRead dyadic dyadicRead ∧
            Cont dyadicRead handoff regseqRead ∧ Cont regseqRead realSeal realRead ∧
              Cont realRead selector pullbackRead ∧
                (hsame row streamRead ∨ hsame row dyadicRead ∨ hsame row regseqRead ∨
                  hsame row realRead ∨ hsame row pullbackRead))
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle pullbackRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro pullbackRead
          ⟨carrier, Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl pullbackRead))))⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowStream =>
            exact Or.inl (hsame_trans (hsame_symm same) rowStream)
        | inr tail =>
            cases tail with
            | inl rowDyadic =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic))
            | inr tail' =>
                cases tail' with
                | inl rowRegseq =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowRegseq)))
                | inr tail'' =>
                    cases tail'' with
                    | inl rowReal =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm same) rowReal))))
                    | inr rowPullback =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm same) rowPullback))))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨requestWindowsStream, streamDyadicRead, dyadicHandoffRegseq,
          regseqRealSealRead, realReadSelectorPullback, source.right⟩
    ledger_sound := by
      intro _row source
      cases source.right with
      | inl rowStream =>
          cases rowStream
          exact ⟨streamUnary, pullbackPkg⟩
      | inr tail =>
          cases tail with
          | inl rowDyadic =>
              cases rowDyadic
              exact ⟨dyadicReadUnary, pullbackPkg⟩
          | inr tail' =>
              cases tail' with
              | inl rowRegseq =>
                  cases rowRegseq
                  exact ⟨regseqReadUnary, pullbackPkg⟩
              | inr tail'' =>
                  cases tail'' with
                  | inl rowReal =>
                      cases rowReal
                      exact ⟨realReadUnary, pullbackPkg⟩
                  | inr rowPullback =>
                      cases rowPullback
                      exact ⟨pullbackUnary, pullbackPkg⟩
  }
  exact ⟨cert, pullbackUnary⟩

end BEDC.Derived.RealWindowBudgetUp
