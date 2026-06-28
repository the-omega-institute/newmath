import BEDC.Derived.RegularCauchyAbsUp.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_public_export_surface [AskSetup] [PackageSetup]
    {X W D V R E H C P N windowRead endpointRead absRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory V ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory publicRead ->
                  Cont X W windowRead ->
                    Cont windowRead D endpointRead ->
                      Cont endpointRead V absRead ->
                        Cont absRead R realRead ->
                          Cont R E realRead ->
                            Cont realRead N publicRead ->
                              PkgSig bundle R pkg ->
                                PkgSig bundle publicRead pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      (hsame row publicRead ∨ hsame row realRead ∨
                                          hsame row R) ∧
                                        UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row W ∨ hsame row D ∨
                                        hsame row V ∨ hsame row R ∨ hsame row E ∨
                                          hsame row H ∨ hsame row C ∨ hsame row P ∨
                                            hsame row N ∨ hsame row realRead ∨
                                              hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont X W windowRead ∧
                                        Cont windowRead D endpointRead ∧
                                          Cont endpointRead V absRead ∧
                                            Cont absRead R realRead ∧ Cont R E realRead ∧
                                              Cont realRead N publicRead ∧
                                                PkgSig bundle R pkg ∧
                                                  PkgSig bundle publicRead pkg)
                                    hsame ∧
                                    UnaryHistory windowRead ∧ UnaryHistory endpointRead ∧
                                      UnaryHistory absRead ∧ UnaryHistory realRead ∧
                                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryX unaryW unaryD unaryV unaryR _unaryE unaryPublic xWindow windowEndpoint
    endpointAbs absReal realSeal realPublic rPkg publicPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryX unaryW xWindow
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed windowUnary unaryD windowEndpoint
  have absUnary : UnaryHistory absRead :=
    unary_cont_closed endpointUnary unaryV endpointAbs
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed absUnary unaryR absReal
  have publicCert :
      SemanticNameCert
        (fun row : BHist =>
          (hsame row publicRead ∨ hsame row realRead ∨ hsame row R) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row realRead ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X W windowRead ∧ Cont windowRead D endpointRead ∧
            Cont endpointRead V absRead ∧ Cont absRead R realRead ∧ Cont R E realRead ∧
              Cont realRead N publicRead ∧ PkgSig bundle R pkg ∧
                PkgSig bundle publicRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead
            (And.intro (Or.inl (hsame_refl publicRead)) unaryPublic)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro row source
        cases source with
        | intro sourceRoute _sourceUnary =>
            cases sourceRoute with
            | inl samePublic =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr samePublic))))))))))
            | inr realOrR =>
                cases realOrR with
                | inl sameReal =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl sameReal))))))))))
                | inr sameR =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameR))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, xWindow, windowEndpoint, endpointAbs, absReal, realSeal,
            realPublic, rPkg, publicPkg⟩
    }
  exact ⟨publicCert, windowUnary, endpointUnary, absUnary, realUnary, unaryPublic⟩

end BEDC.Derived.RegularCauchyAbsUp
