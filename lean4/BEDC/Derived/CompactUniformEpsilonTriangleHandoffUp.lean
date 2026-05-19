import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactUniformEpsilonTriangleHandoffCarrier [AskSetup] [PackageSetup]
    (X Y center x xp eps mu rho dx dxp dy dyp H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory center ∧ UnaryHistory x ∧
    UnaryHistory xp ∧ UnaryHistory eps ∧ UnaryHistory mu ∧ UnaryHistory rho ∧
      UnaryHistory dx ∧ UnaryHistory dxp ∧ UnaryHistory dy ∧ UnaryHistory dyp ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle N pkg

theorem CompactUniformEpsilonTriangleHandoff_namecert_obligations [AskSetup] [PackageSetup]
    {X Y center x xp eps mu rho dx dxp dy dyp H C P N sourceTriangle targetTriangle output :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformEpsilonTriangleHandoffCarrier
        X Y center x xp eps mu rho dx dxp dy dyp H C P N bundle pkg ->
      Cont dx dxp sourceTriangle ->
        Cont dy dyp targetTriangle ->
          Cont sourceTriangle targetTriangle output ->
            PkgSig bundle output pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row output ∧ UnaryHistory row)
                  (fun row : BHist => hsame row output)
                  (fun row : BHist => hsame row output ∧
                    Cont sourceTriangle targetTriangle output)
                  hsame ∧
                UnaryHistory center ∧ UnaryHistory dx ∧ UnaryHistory dxp ∧
                  UnaryHistory dy ∧ UnaryHistory dyp ∧ UnaryHistory sourceTriangle ∧
                    UnaryHistory targetTriangle ∧ UnaryHistory output ∧
                      Cont dx dxp sourceTriangle ∧ Cont dy dyp targetTriangle ∧
                        Cont sourceTriangle targetTriangle output ∧ PkgSig bundle output pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute targetRoute outputRoute outputPkg
  obtain
    ⟨_unaryX, _unaryY, centerUnary, _xUnary, _xpUnary, _epsUnary, _muUnary,
      _rhoUnary, dxUnary, dxpUnary, dyUnary, dypUnary, _hUnary, _cUnary, _pUnary,
      _nUnary, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceTriangle :=
    unary_cont_closed dxUnary dxpUnary sourceRoute
  have targetUnary : UnaryHistory targetTriangle :=
    unary_cont_closed dyUnary dypUnary targetRoute
  have outputUnary : UnaryHistory output :=
    unary_cont_closed sourceUnary targetUnary outputRoute
  have sourceAtOutput : hsame output output ∧ UnaryHistory output :=
    ⟨hsame_refl output, outputUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row output ∧ UnaryHistory row)
          (fun row : BHist => hsame row output)
          (fun row : BHist => hsame row output ∧ Cont sourceTriangle targetTriangle output)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro output sourceAtOutput
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, outputRoute⟩
  }
  exact
    ⟨cert, centerUnary, dxUnary, dxpUnary, dyUnary, dypUnary, sourceUnary, targetUnary,
      outputUnary, sourceRoute, targetRoute, outputRoute, outputPkg⟩

end BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp
