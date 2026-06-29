import BEDC.Derived.KuratowskiEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KuratowskiEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KuratowskiEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M B D T I _H _C _P _N distanceRead targetRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory D ->
          UnaryHistory T ->
            UnaryHistory I ->
              Cont M B distanceRead ->
                Cont distanceRead D targetRead ->
                  Cont targetRead I routeRead ->
                    PkgSig bundle routeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨
                              hsame row I ∨ hsame row routeRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle routeRead pkg)
                          hsame ∧
                        UnaryHistory distanceRead ∧ UnaryHistory targetRead ∧
                          UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro mUnary bUnary dUnary _tUnary iUnary distanceRoute targetRoute routeRoute routePkg
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed mUnary bUnary distanceRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed distanceUnary dUnary targetRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed targetUnary iUnary routeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨ hsame row I ∨
              hsame row routeRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact ⟨source.right, routePkg⟩
  }
  exact ⟨cert, distanceUnary, targetUnary, routeUnary⟩

theorem KuratowskiEmbedding_distance_readback_exactness [AskSetup] [PackageSetup]
    {M B D T I _H _C _P _N metricRead realRead _targetRead isoRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory D ->
          UnaryHistory T ->
            UnaryHistory I ->
              Cont M D metricRead ->
                Cont metricRead T realRead ->
                  Cont realRead I isoRead ->
                    PkgSig bundle isoRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row isoRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row D ∨ hsame row T ∨ hsame row I ∨
                              hsame row isoRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle isoRead pkg)
                          hsame ∧
                        UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                          UnaryHistory isoRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro mUnary _bUnary dUnary tUnary iUnary metricRoute realRoute isoRoute isoPkg
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed mUnary dUnary metricRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed metricUnary tUnary realRoute
  have isoUnary : UnaryHistory isoRead :=
    unary_cont_closed realUnary iUnary isoRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row isoRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row T ∨ hsame row I ∨ hsame row isoRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle isoRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro isoRead ⟨hsame_refl isoRead, isoUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, isoPkg⟩
  }
  exact ⟨cert, metricUnary, realUnary, isoUnary⟩

end BEDC.Derived.KuratowskiEmbeddingUp
