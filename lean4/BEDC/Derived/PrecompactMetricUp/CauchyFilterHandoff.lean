import BEDC.Derived.PrecompactMetricUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PrecompactMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PrecompactMetric_cauchy_filter_handoff_obligations [AskSetup] [PackageSetup]
    {X D N F R M H C G Q filterRead regularRead basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X D filterRead ->
      Cont filterRead F regularRead ->
        Cont regularRead R basisRead ->
          PkgSig bundle Q pkg ->
            UnaryHistory X ->
              UnaryHistory D ->
                UnaryHistory F ->
                  UnaryHistory R ->
                    SemanticNameCert
                        (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row D ∨ hsame row N ∨ hsame row F ∨
                            hsame row R ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                              hsame row G ∨ hsame row Q ∨ hsame row filterRead ∨
                                hsame row regularRead ∨ hsame row basisRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont X D filterRead ∧
                            Cont filterRead F regularRead ∧
                              Cont regularRead R basisRead ∧ PkgSig bundle Q pkg)
                        hsame ∧
                      UnaryHistory filterRead ∧ UnaryHistory regularRead ∧
                        UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro filterCont regularCont basisCont pkgQ unaryX unaryD unaryF unaryR
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed unaryX unaryD filterCont
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed filterUnary unaryF regularCont
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed regularUnary unaryR basisCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row D ∨ hsame row N ∨ hsame row F ∨ hsame row R ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨ hsame row Q ∨
                hsame row filterRead ∨ hsame row regularRead ∨ hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X D filterRead ∧ Cont filterRead F regularRead ∧
              Cont regularRead R basisRead ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro basisRead ⟨hsame_refl basisRead, basisUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, filterCont, regularCont, basisCont, pkgQ⟩
  }
  exact ⟨cert, filterUnary, regularUnary, basisUnary⟩

end BEDC.Derived.PrecompactMetricUp
