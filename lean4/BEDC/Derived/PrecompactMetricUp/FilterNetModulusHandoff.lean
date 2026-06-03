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

theorem PrecompactMetric_filter_net_modulus_handoff [AskSetup] [PackageSetup]
    {X D N F R M H C G Q netRead modulusRead filterRead basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont N M netRead →
      Cont netRead F modulusRead →
        Cont modulusRead R filterRead →
          Cont filterRead C basisRead →
            PkgSig bundle Q pkg →
              UnaryHistory N →
                UnaryHistory M →
                  UnaryHistory F →
                    UnaryHistory R →
                      UnaryHistory C →
                        SemanticNameCert
                            (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row X ∨ hsame row D ∨ hsame row N ∨
                                hsame row F ∨ hsame row R ∨ hsame row M ∨
                                  hsame row H ∨ hsame row C ∨ hsame row G ∨
                                    hsame row Q ∨ hsame row netRead ∨
                                      hsame row modulusRead ∨ hsame row filterRead ∨
                                        hsame row basisRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont N M netRead ∧
                                Cont netRead F modulusRead ∧
                                  Cont modulusRead R filterRead ∧
                                    Cont filterRead C basisRead ∧ PkgSig bundle Q pkg)
                            hsame ∧
                          UnaryHistory netRead ∧ UnaryHistory modulusRead ∧
                            UnaryHistory filterRead ∧ UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro netCont modulusCont filterCont basisCont pkgQ unaryN unaryM unaryF unaryR unaryC
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed unaryN unaryM netCont
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed netUnary unaryF modulusCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed modulusUnary unaryR filterCont
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed filterUnary unaryC basisCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row D ∨ hsame row N ∨ hsame row F ∨ hsame row R ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨ hsame row Q ∨
                hsame row netRead ∨ hsame row modulusRead ∨ hsame row filterRead ∨
                  hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N M netRead ∧ Cont netRead F modulusRead ∧
              Cont modulusRead R filterRead ∧ Cont filterRead C basisRead ∧
                PkgSig bundle Q pkg)
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, netCont, modulusCont, filterCont, basisCont, pkgQ⟩
  }
  exact ⟨cert, netUnary, modulusUnary, filterUnary, basisUnary⟩

end BEDC.Derived.PrecompactMetricUp
