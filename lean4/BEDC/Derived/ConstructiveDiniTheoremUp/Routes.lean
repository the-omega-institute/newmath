import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConstructiveDiniTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConstructiveDiniTheoremMonotoneUniformRoute [AskSetup] [PackageSetup]
    {K F M D U W R E H C P N uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
        UnaryHistory F ->
          UnaryHistory M ->
            UnaryHistory D ->
              UnaryHistory W ->
                UnaryHistory E ->
                  Cont K F M ->
                    Cont M D U ->
                      Cont U W R ->
                        Cont R E uniformRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle uniformRead pkg ->
                              SemanticNameCert
                          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row F ∨ hsame row M ∨ hsame row D ∨
                              hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                                hsame row uniformRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle uniformRead pkg ∧
                              PkgSig bundle P pkg)
                          hsame ∧
                                UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryK unaryF _unaryM unaryD unaryW unaryE routeM routeU routeR routeUniform pPkg
    uniformPkg
  have unaryMFromRoute : UnaryHistory M :=
    unary_cont_closed unaryK unaryF routeM
  have unaryU : UnaryHistory U :=
    unary_cont_closed unaryMFromRoute unaryD routeU
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryU unaryW routeR
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed unaryR unaryE routeUniform
  have sourceAtUniform : hsame uniformRead uniformRead ∧ UnaryHistory uniformRead :=
    ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row M ∨ hsame row D ∨ hsame row U ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle uniformRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceAtUniform
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, uniformPkg, pPkg⟩
  }
  exact ⟨cert, uniformUnary⟩

theorem ConstructiveDiniTheoremFiniteNetMonotoneWindowRoute [AskSetup] [PackageSetup]
    {K F M D U W R E H C P N finiteWindow modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory F ->
      UnaryHistory M ->
        UnaryHistory D ->
          Cont K M finiteWindow ->
            Cont finiteWindow D modulusRead ->
              Cont modulusRead U W ->
                PkgSig bundle P pkg ->
                  PkgSig bundle modulusRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row F ∨ hsame row M ∨
                            hsame row finiteWindow ∨ hsame row D ∨ hsame row modulusRead ∨
                              hsame row U ∨ hsame row W)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont K M finiteWindow ∧
                            Cont finiteWindow D modulusRead ∧ PkgSig bundle modulusRead pkg)
                        hsame ∧
                      UnaryHistory finiteWindow ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryK _unaryF unaryM unaryD finiteRoute modulusRoute _windowRoute _pPkg modulusPkg
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed unaryK unaryM finiteRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed finiteUnary unaryD modulusRoute
  have sourceAtModulus : hsame modulusRead modulusRead ∧ UnaryHistory modulusRead :=
    ⟨hsame_refl modulusRead, modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row M ∨ hsame row finiteWindow ∨
              hsame row D ∨ hsame row modulusRead ∨ hsame row U ∨ hsame row W)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K M finiteWindow ∧ Cont finiteWindow D modulusRead ∧
              PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, finiteRoute, modulusRoute, modulusPkg⟩
  }
  exact ⟨cert, finiteUnary, modulusUnary⟩

end BEDC.Derived.ConstructiveDiniTheoremUp
